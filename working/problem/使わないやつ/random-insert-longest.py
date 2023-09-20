# adding the longest clause
# insertion position is random

import json
import pathlib
import subprocess
import sys
import time
import re

import random
import shutil

# experiment name
EXPERIMENT_NAME = "random-insert-longest"

# kissat = "/root/kissat"
# drattrim = "/root/drat-trim"

kissat = "kissat"
drattrim = "drat-trim"

def no_d(drat_proof_list):
    return [clause for clause in drat_proof_list if clause[0] != "d"]

def avg_len(clauses_list):
    split_l = [len(l.split())-1 for l in clauses_list]
    return sum(split_l) / len(split_l)

# without duplication, consider x_n and -x_n to be the same
def get_added_vcount(clauses_list):
    # getting max var_n
    max_var_n = 0
    for clause in clauses_list:
        clause_split = clause.split()[:-1]
        clause_max = max([abs(int(v)) for v in clause_split])
        max_var_n = max(max_var_n, clause_max)
    # counting occurrences of var
    var_list = [0] * (max_var_n + 1)
    for clause in clauses_list:       
        for v in clause.split()[:-1]: var_list[abs(int(v))] += 1
    return len([i for i in var_list if i > 0])
    
        

def extract_clauses(drat_proof_path, data):
    extracted_clauses_list = []
    extracted_all_clauses_list = []
    # extracting clauses
    with open(drat_proof_path) as f:
        drat_proof_list = no_d(f.readlines())[:-1]
    # if proof length is 0 or not
    if len(drat_proof_list) == 0:
        return [], []
    else:
        longest_clause = ""
        longest_clause_pos = -1
        for i in range(len(drat_proof_list)):
            if len(longest_clause.split()) < len(drat_proof_list[i].split()):
                longest_clause = drat_proof_list[i]
                longest_clause_pos = i
        extracted_clauses_list = [longest_clause]
        extracted_all_clauses_list = drat_proof_list[:longest_clause_pos+1]
        
    # adding infomation to data
    data["last_index"] = longest_clause_pos
    len_of_extracted_clauses_list = [len(l.split()) for l in extracted_clauses_list]
    data["max_len_of_extracted_clauses"] = max(len_of_extracted_clauses_list)
    data["min_len_of_extracted_clauses"] = min(len_of_extracted_clauses_list)
    data["avg_len_of_extracted_clauses"] = avg_len(extracted_clauses_list)
    len_of_extracted_all_clauses_list = [len(l.split()) for l in extracted_all_clauses_list]
    
    data["max_len_of_extracted_all_clauses"] = max(len_of_extracted_all_clauses_list)
    data["min_len_of_extracted_all_clauses"] = min(len_of_extracted_all_clauses_list)
    data["avg_len_of_extracted_all_clauses"] = avg_len(extracted_all_clauses_list)
    data["num_of_adding_clauses"] = len(extracted_clauses_list)    
    data["added_vcount_with_dup"] = data["avg_len_of_extracted_clauses"] * data["num_of_adding_clauses"]
    data["added_vcount_without_dup"] = get_added_vcount(extracted_clauses_list)

    return [extracted_clauses_list, extracted_all_clauses_list]

def make_all_path(filename):
    filename = sys.argv[1]
    bench_path = pathlib.Path(filename)
    unzip_bench = filename.rstrip(".bz2")
    subprocess.run(["bzip2", "-dk", str(bench_path)])
    unzip_bench_path = pathlib.Path(unzip_bench)
    drat_proof_path = pathlib.Path("drat-proof.drat")
    drat_proof_path.touch()
    trimmed_drat_proof_path = pathlib.Path("trimmed-drat-proof.drat")
    trimmed_drat_proof_path.touch()
    return [unzip_bench_path, drat_proof_path, trimmed_drat_proof_path]

def exec_kissat(unzip_bench_path, drat_proof_path, data):
    kissat_command = [kissat, "-q", "-n", str(unzip_bench_path), "--no-binary", str(drat_proof_path)]
    returncode = subprocess.run(kissat_command, stdout=subprocess.DEVNULL).returncode
    if returncode in [10, 20]: return returncode
    else:
        data["kissat_returncode"] = returncode
        json.dump(data, fp=sys.stdout, indent=4)
        unzip_bench_path.unlink()
        drat_proof_path.unlink()
        trimmed_drat_proof_path.unlink()
        exit(1)

def exec_drattrim(unzip_bench_path, drat_proof_path, trimmed_drat_proof_path, data):
    
    drattrim_command = [drattrim, str(unzip_bench_path), str(drat_proof_path), "-l", str(trimmed_drat_proof_path)]
    exec_res = subprocess.run(drattrim_command, capture_output=True, text=True)
    stdout = exec_res.stdout
    returncode = exec_res.returncode
    if returncode == 0:
        clause_num = re.search("[0-9]+ of [0-9]+ lemmas", stdout)
        if clause_num == None:
            data["drat_trim_returncode"] = returncode
            data["drat_trim_output"] = stdout
            json.dump(data, fp=sys.stdout, indent=4)
            unzip_bench_path.unlink()
            drat_proof_path.unlink()
            trimmed_drat_proof_path.unlink()
            exit(1)
        else:
            clause_num = list(map(int, re.findall("[0-9]+", clause_num.group())))
            return clause_num
    else:
        data["drat_trim_returncode"] = returncode
        data["drat_trim_output"] = stdout
        json.dump(data, fp=sys.stdout, indent=4)
        unzip_bench_path.unlink()
        drat_proof_path.unlink()
        trimmed_drat_proof_path.unlink()
        exit(1)

def avg_len_of_clauses(drat_proof_path):
    with open(str(drat_proof_path)) as f:
        drat_proof_list = no_d(f.readlines())
    return avg_len(drat_proof_list)
        
def make_new_problem(unzip_bench_path, drat_proof_path, data):
    extracted_list = extract_clauses(drat_proof_path, data)
    extracted_clauses_list = extracted_list[0]
    extracted_all_clauses_list = extracted_list[1]
    with open(str(unzip_bench_path)) as f:
        original_problem_list = f.readlines()
    new_problem_list = original_problem_list.copy()
    new_problem_p = new_problem_list.pop(0)
    num_of_clause = int(new_problem_p.split()[3])
    new_num_of_clause = num_of_clause + len(extracted_clauses_list)
    new_problem_p_list = new_problem_p.split()
    new_problem_p_list[3] = str(new_num_of_clause)
    new_problem_p = " ".join(new_problem_p_list) + "\n"

    insert_index = random.randrange(len(new_problem_list)+1)
    data["insert_index"] = insert_index
    insert_list = extracted_clauses_list[0] if extracted_clauses_list != [] else ""
    new_problem_list.insert(insert_index, insert_list)
    new_problem_list = [new_problem_p] + new_problem_list
    
    with open(str(unzip_bench_path), mode="w") as f:
        f.writelines(new_problem_list)
    return original_problem_list, extracted_all_clauses_list

def exec_kissat_and_drattrim_again(unzip_bench_path, drat_proof_path, trimmed_drat_proof_path, original_problem_list, extracted_all_clauses_list, data):
    t0 = time.perf_counter()
    exec_kissat(unzip_bench_path, drat_proof_path, data)
    t1 = time.perf_counter()
    data["kissat_time"] = t1 - t0
    with open(str(unzip_bench_path), mode="w") as f:
        f.writelines(original_problem_list)
    with open(str(drat_proof_path)) as f:
        new_drat_proof_list = f.readlines()
    with open(str(drat_proof_path), mode="w") as f:
        f.writelines(extracted_all_clauses_list + new_drat_proof_list)
    t0 = time.perf_counter()
    data["aft_clause_num"], data["bef_clause_num"] = exec_drattrim(unzip_bench_path, drat_proof_path, trimmed_drat_proof_path, data)
    t1 = time.perf_counter()
    data["drat_trim_time"] = t1 - t0
    data["new_avg_len_of_clauses_in_proof"] = avg_len_of_clauses(drat_proof_path)
    data["new_avg_len_of_clauses_in_trimmed_proof"]= avg_len_of_clauses(trimmed_drat_proof_path)

def exec_kissat_drattrim_multiple(unzip_bench_path,
                                  drat_proof_path,
                                  trimmed_drat_proof_path,
                                  data):
    cp_trimmed_drat_proof_path = pathlib.Path("cp-drat-trimmed-drat-proof.drat")
    shutil.copy(str(trimmed_drat_proof_path),
                str(cp_trimmed_drat_proof_path))
    data["min_time"] = "1st"

    # 5 times
    # extracting clauses from copied proof
    for time in ["1st", "2nd", "3rd", "4th", "5th"]:
        original_problem_list, extracted_all_clauses_list = make_new_problem(unzip_bench_path, cp_trimmed_drat_proof_path, data)
        exec_kissat_and_drattrim_again(unzip_bench_path,
                                       drat_proof_path,
                                       trimmed_drat_proof_path,
                                       original_problem_list,
                                       extracted_all_clauses_list,
                                       data)
        key_list = ["bef_clause_num",
                    "aft_clause_num",
                    "insert_index",
                    "last_index",
                    "max_len_of_extracted_clauses",
                    "min_len_of_extracted_clauses",
                    "avg_len_of_extracted_clauses",
                    "max_len_of_extracted_all_clauses",
                    "min_len_of_extracted_all_clauses",
                    "avg_len_of_extracted_all_clauses",
                    "num_of_adding_clauses",
                    "added_vcount_with_dup",
                    "added_vcount_without_dup",
                    "kissat_time",
                    "drat_trim_time",
                    "new_avg_len_of_clauses_in_proof",
                    "new_avg_len_of_clauses_in_trimmed_proof"]
        for key in key_list:
            data[time+"_"+key] = data[key]
        if data[time+"_"+"aft_clause_num"] < data[data["min_time"]+"_aft_clause_num"]:
            data["min_time"] = time
        for key in key_list:
            data[key] = data[data["min_time"]+"_"+key]
        json.dump(data, fp=sys.stdout, indent=4)        
    cp_trimmed_drat_proof_path.unlink()



if __name__ == "__main__":   
    filename = sys.argv[1]
    path_list = make_all_path(filename)
    unzip_bench_path = path_list[0]
    drat_proof_path = path_list[1]
    trimmed_drat_proof_path = path_list[2]

    # infomation to output
    data = {"bench":filename,
            "res":"unknown",
            "experiment":EXPERIMENT_NAME,

            "min_time":"",
            
            "bef_clause_num":0,
            "aft_clause_num":0,
            "insert_index":0,
            "last_index":0,
            "max_len_of_extracted_clauses":0,
            "min_len_of_extracted_clauses":0,
            "avg_len_of_extracted_clauses":0,
            "max_len_of_extracted_all_clauses":0,
            "min_len_of_extracted_all_clauses":0,
            "avg_len_of_extracted_all_clauses":0,
            "num_of_adding_clauses":0,
            "added_vcount_with_dup":0,
            "added_vcount_without_dup":0,
            "kissat_time":0,
            "drat_trim_time":0,
            "new_avg_len_of_clauses_in_proof":0,
            "new_avg_len_of_clauses_in_trimmed_proof":0,

            "1st_bef_clause_num":0,
            "1st_aft_clause_num":0,
            "1st_insert_index":0,
            "1st_last_index":0,
            "1st_max_len_of_extracted_clauses":0,
            "1st_min_len_of_extracted_clauses":0,
            "1st_avg_len_of_extracted_clauses":0,
            "1st_max_len_of_extracted_all_clauses":0,
            "1st_min_len_of_extracted_all_clauses":0,
            "1st_avg_len_of_extracted_all_clauses":0,
            "1st_num_of_adding_clauses":0,
            "1st_added_vcount_with_dup":0,
            "1st_added_vcount_without_dup":0,
            "1st_kissat_time":0,
            "1st_drat_trim_time":0,
            "1st_new_avg_len_of_clauses_in_proof":0,
            "1st_new_avg_len_of_clauses_in_trimmed_proof":0,

            "2nd_bef_clause_num":0,
            "2nd_aft_clause_num":0,
            "2nd_insert_index":0,
            "2nd_last_index":0,
            "2nd_max_len_of_extracted_clauses":0,
            "2nd_min_len_of_extracted_clauses":0,
            "2nd_avg_len_of_extracted_clauses":0,
            "2nd_max_len_of_extracted_all_clauses":0,
            "2nd_min_len_of_extracted_all_clauses":0,
            "2nd_avg_len_of_extracted_all_clauses":0,
            "2nd_num_of_adding_clauses":0,
            "2nd_added_vcount_with_dup":0,
            "2nd_added_vcount_without_dup":0,
            "2nd_kissat_time":0,
            "2nd_drat_trim_time":0,
            "2nd_new_avg_len_of_clauses_in_proof":0,
            "2nd_new_avg_len_of_clauses_in_trimmed_proof":0,

            "3rd_bef_clause_num":0,
            "3rd_aft_clause_num":0,
            "3rd_insert_index":0,
            "3rd_last_index":0,
            "3rd_max_len_of_extracted_clauses":0,
            "3rd_min_len_of_extracted_clauses":0,
            "3rd_avg_len_of_extracted_clauses":0,
            "3rd_max_len_of_extracted_all_clauses":0,
            "3rd_min_len_of_extracted_all_clauses":0,
            "3rd_avg_len_of_extracted_all_clauses":0,
            "3rd_num_of_adding_clauses":0,
            "3rd_added_vcount_with_dup":0,
            "3rd_added_vcount_without_dup":0,
            "3rd_kissat_time":0,
            "3rd_drat_trim_time":0,
            "3rd_new_avg_len_of_clauses_in_proof":0,
            "3rd_new_avg_len_of_clauses_in_trimmed_proof":0,

            "4th_bef_clause_num":0,
            "4th_aft_clause_num":0,
            "4th_insert_index":0,
            "4th_last_index":0,
            "4th_max_len_of_extracted_clauses":0,
            "4th_min_len_of_extracted_clauses":0,
            "4th_avg_len_of_extracted_clauses":0,
            "4th_max_len_of_extracted_all_clauses":0,
            "4th_min_len_of_extracted_all_clauses":0,
            "4th_avg_len_of_extracted_all_clauses":0,
            "4th_num_of_adding_clauses":0,
            "4th_added_vcount_with_dup":0,
            "4th_added_vcount_without_dup":0,
            "4th_kissat_time":0,
            "4th_drat_trim_time":0,
            "4th_new_avg_len_of_clauses_in_proof":0,
            "4th_new_avg_len_of_clauses_in_trimmed_proof":0,

            "5th_bef_clause_num":0,
            "5th_aft_clause_num":0,
            "5th_insert_index":0,
            "5th_last_index":0,
            "5th_max_len_of_extracted_clauses":0,
            "5th_min_len_of_extracted_clauses":0,
            "5th_avg_len_of_extracted_clauses":0,
            "5th_max_len_of_extracted_all_clauses":0,
            "5th_min_len_of_extracted_all_clauses":0,
            "5th_avg_len_of_extracted_all_clauses":0,
            "5th_num_of_adding_clauses":0,
            "5th_added_vcount_with_dup":0,
            "5th_added_vcount_without_dup":0,
            "5th_kissat_time":0,
            "5th_drat_trim_time":0,
            "5th_new_avg_len_of_clauses_in_proof":0,
            "5th_new_avg_len_of_clauses_in_trimmed_proof":0,            
            
            "kissat_returncode":-1,
            "drat_trim_returncode":-1,
            "drat_trim_output":""}

    # Solving the (UN)SAT problem
    returncode = exec_kissat(unzip_bench_path, drat_proof_path, data)
    
    # Returncode of kissat
    if returncode not in [10, 20]:
        print("Unexpected Return Code from kissat: ", returncode, file=sys.stderr)
        print("  file: ", str(unzip_bench_path), file=sys.stderr)
        exit(1)
    if returncode == 10:
        data["res"] = "SAT"
    elif returncode == 20:
        data["res"] = "UNSAT"
        exec_drattrim(unzip_bench_path, drat_proof_path, trimmed_drat_proof_path, data)       
        exec_kissat_drattrim_multiple(unzip_bench_path,
                                      drat_proof_path,
                                      trimmed_drat_proof_path,
                                      data)
    
    unzip_bench_path.unlink()
    drat_proof_path.unlink()
    trimmed_drat_proof_path.unlink()

    json.dump(data, fp=sys.stdout, indent=4)
        
