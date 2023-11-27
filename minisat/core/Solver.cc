/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdlib.h> // ファイル読み込みのために


#include <math.h>

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"

#include <inttypes.h> // int64_t型を出力する際のPRId32を使うため

#include <string>
#include <string.h> //文字列の長さの取得のため

#include <fstream> // ファイルから入力を受け取れるように->getProofLength()

using namespace Minisat;

using namespace std;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    // Solver.hの中のクラスSolverの中で定義したパラメータに値を代入する
    // => ここでのパラメータはSolver.hの中で定義されていないといけない
    verbosity        (0)
  , proof_file       (NULL)
  , restore_file     ("")
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , min_learnts_lim  (opt_min_learnts_lim)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , watches            (WatcherDeleted(ca))
  , order_heap         (VarOrderLt(activity))
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , next_var           (0)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)

  // 復元(介入)の際に使う
  , next_intervention (0) 
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(lbool upol, bool dvar)
{
    Var v;
    if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }else
        v = next_var++;

    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .insert(v, 0);
    polarity .insert(v, true);
    user_pol .insert(v, upol);
    decision .reserve(v); // 多分vの値を入れられるように拡張してる
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
void Solver::releaseVar(Lit l)
{
    if (value(l) == l_Undef){
        addClause(l);
        released_vars.push(var(l));
    }
}

// SimpSolver::addClause_()と同様に、
// 問題を読み込む際にSolver::addClause_()は問題の節の数だけ実行される
// 既に節がtrueとなるものとfalseなリテラルを取り除いた節の大きさが1の時は追加しない
// 上記の節の数 + 実際にclausesに追加する節の数 = 問題の節の数
// (例外的だと考えているが同じ変数の肯定と否定が含まれる節がある場合はそれも追加しない)
bool Solver::addClause_(vec<Lit>& ps)
{
    // printf("実行開始:Solver::addClause_()\n");
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // printf(" addClause_()を実行します\n");
    // Check if clause is satisfied and remove false/duplicate literals:
    // sortをすることで絶対値昇順(同じ場合は+(肯定),-(否定)の順で)にソートされる
    // 肯定と否定が連続して入ってくる
    // addClauseとanalyzeの節は一緒？
    // => 一緒じゃない(addClauseは問題の節追加しかない)
    // => analyzeでの節の追加はどこでやってる？
    // printf("addClause\n");
    // 証明部分
    if (proof_file){
        for (int k=0; k<ps.size(); k++){
            fprintf(proof_file, "%s%d ", (sign(ps[k])? "-" : ""), var(ps[k])+1);
        }
        fprintf(proof_file, "0\n");
    }
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        // 否定と肯定が入っている場合？
        if (value(ps[i]) == l_True || ps[i] == ~p){
            // printf("ps[i]=%s%d, ~p=%s%d\n", (sign(ps[i])? "-" : ""), var(ps[i])+1, (sign(~p)? "-" : ""), var(~p)+1);
            // printf("value(ps[i]) == l_True = %s || ps[i] == ~p = %s\n", (value(ps[i]) == l_True)? "true" : "false", (ps[i] == ~p)? "true" : "false");
            return true;
        }
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);
    // 証明部分
    if (proof_file){
        for (int k=0; k<ps.size(); k++){
            fprintf(proof_file, "%s%d ", (sign(ps[k])? "-" : ""), var(ps[k])+1);
        }
        fprintf(proof_file, "0\n");
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        // printf("ps.size() == 1\n");
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


// 問題を読み込んだ時の節の数(num_clauses)はattachClause()の呼び出し回数に一致する
// detachClause()は呼び出されない(num_clausesは減少しない)
void Solver::attachClause(CRef cr){
    // printf("実行開始:attachClause()\n");
    const Clause& c = ca[cr]; // ca:clauseAllocater -> core/Solver.h
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) num_learnts++, learnts_literals += c.size();
    else            num_clauses++, clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict){
    // printf("実行開始:detachClause()\n");
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    // Strict or lazy detaching:
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) num_learnts--, learnts_literals -= c.size();
    else            num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    if (proof_file) {
        // fprintf(proof_file, "CRef cr = %d", cr);
        fprintf(proof_file, "d ");
        for (int k = 0; k < ca[cr].size(); k++) {
            fprintf(proof_file, "%s%d ", (sign(ca[cr][k])? "-" : ""), var(ca[cr][k])+1);
        }
        fprintf(proof_file, "0\n");
    }
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
                polarity[x] = sign(trail[c]); // polarityを決めるのはここだけ(初期値はtrue)
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:

// 候補を決める
// 今回はorder_heapからわかるスコアが大きい変数を上から３つ
void Solver::getCandidates(){

    // order_heapの(ほぼ)複製
    IntMap<Var,int,MkIndexDefault<Var>> indices;
    vec<Var>                            heap;
    order_heap.indices.copyTo(indices);
    order_heap.heap   .copyTo(heap   );

    for (int j=0;j<10;){
        // heapの中でスコア最大の変数を得る(removeMin())
        Var v            = heap[0];
        heap[0]          = heap.last();
        indices[heap[0]] = 0;
        indices[v]       = -1;
        heap.pop();
        if (heap.size() > 1) {
            // percolateDown(i=0)
            int i = 0;
            Var x = heap[i];
            while (i*2+1 < heap.size()){
                int child = (i+1)*2 < heap.size() && activity[heap[(i+1)*2]] > activity[heap[i*2+1]] ? (i+1)*2 : i*2+1;
                if (!(activity[heap[child]] > activity[x])) break;
                heap[i]          = heap[child];
                indices[heap[i]] = i;
                i                = child;
            }
            heap   [i] = x;
            indices[x] = i;
        }
        
        // 既に割当済みでなければ候補に追加する
        if (value(v) == l_Undef){
            candidates.push(v);
            j++;
        }

    }
}

// 今のタイミングまでの介入の情報を今のタイミングの選択部分(-2)を受け取った候補に変えた上でファイルに書き込む
void Solver::writeSubIntervention(Var candidate){

    FILE* f = fopen("sub-intervention", "w"); // interventionでも良いけど書き直すの面倒だから
    if (f == NULL){
        printf("ファイルオープンに失敗しました:sub-intervention\n");
    }

    fprintf(f, "i %d\n", next_intervention+1); // 介入の回数(今のタイミングまで)

    // 今のタイミングまでの介入
    for (int j=0; j<next_intervention; j++){
        fprintf(f, "t %d\n", usr_interventions[j]); // タイミング(何回目の変数選択で介入するか)
        fprintf(f, "p %d\n", usr_picks[j]);         // 変数選択(どの変数を選択するか)
    }

    // 選択部分を候補に変えた今のタイミングの介入
    assert(usr_picks[next_intervention] == -2);
    fprintf(f, "t %d\n", usr_interventions[next_intervention]);
    fprintf(f, "p %d\n", candidate);

    fclose(f);
}

// 問題, 証明, 介入ファイルを決めてminisatを実行する(追加オプションがあるならその都度コード書き換えて)
void Solver::execMinisat(char* prob, char* proof, char* intervention){
    int MAX_LEN = 1000;      // コマンドの最大文字数
    char command[MAX_LEN];  // コマンド
    char* minisat = "/root/minisat/build/release/bin/minisat";
    sprintf(command, "%s %s -proof=%s -intervention=%s -verb=-1 > res", minisat, prob, proof, intervention);
    // sprintf(command, "%s %s -proof=%s -intervention=%s -verb=-1", minisat, prob, proof, intervention);
    system(command);
}

// 解いた結果から必要な情報を出力する
void Solver::print_result(char* result){
    ifstream ifs(result);
    if (ifs.fail()) {printf("ファイルオープンに失敗しました:%s\n", result);exit(1);}
    string str;
    string value;
    while (getline(ifs, str)) {
        if (str.find("restarts              : ") != string::npos) {
            value = str.substr(strlen("restarts              : "));
            value = value.substr(0, value.find(" "));
            printf("   restarts=%s\n", value.c_str());
        } else if (str.find("conflicts             : ") != string::npos) {
            value = str.substr(strlen("conflicts             : "));
            value = value.substr(0, value.find(" "));
            printf("   conflicts=%s\n", value.c_str());
        } else if (str.find("decisions             : ") != string::npos) {
            value = str.substr(strlen("decisions             : "));
            value = value.substr(0, value.find(" "));
            printf("   decision=%s\n", value.c_str());
        } else if (str.find("propagations          : ") != string::npos) {
            value = str.substr(strlen("propagations          : "));
            value = value.substr(0, value.find(" "));
            printf("   propagations=%s\n", value.c_str());
        } else if (str.find("conflict literals     : ") != string::npos) {
            value = str.substr(strlen("conflict literals     : "));
            value = value.substr(0, value.find(" "));
            printf("   conflict literals=%s\n", value.c_str());
        } else if (str.find("Memory used           : ") != string::npos) {
            value = str.substr(strlen("Memory used           : "));
            value = value.substr(0, value.find(" "));
            printf("   Memory used=%s\n", value.c_str());
        } else if (str.find("CPU time              : ") != string::npos) {
            value = str.substr(strlen("CPU time              : "));
            value = value.substr(0, value.find(" "));
            printf("   CPU time=%s\n", value.c_str());
        }
    }
}

// 問題, 証明, 短縮後の証明を決めてdrat-trimを実行する(追加オプションがあるならその都度コード書き換えて)
void Solver::execDrattrim(char* prob, char* proof, char* trimed_proof){
    int MAX_LEN = 1000;      // コマンドの最大文字数
    char command[MAX_LEN];  // コマンド
    char* drattrim = "/root/drat-trim";
    sprintf(command, "%s %s %s -l %s > res", drattrim, prob, proof, trimed_proof);
    system(command);
}

// 証明を受け取って長さを返す
int Solver::getProofLength(char* proof){
    ifstream ifs(proof);
    if (ifs.fail()) {printf("ファイルオープンに失敗しました:%s\n", proof);exit(1);}
    string str;
    int ret = 0;
    while (getline(ifs, str)) {
        if (str[0] != 'd') ret += 1;
    }
    ifs.close();
    return ret;
}

// 候補を選んでその中から一番有効な変数を選択する(有効の比較は証明の長さなど)
Var Solver::selectFromCandidateVars(){

    printf("開始:selectFromCandidateVars()\n");
    printf(" decisions=%d\n", decisions);

    // 使用する変数
    Var ret = var_Undef;    // 一番有効な変数を入れる
    int min_length = -1;
    int ret_i = -1;         // 一番有効な変数が何番目にあったか

    // 候補となる変数らを決定する(受け取る)
    candidates.clear();
    getCandidates();
    for (int i=0;i<candidates.size();i++){
        printf(" candidates[%2d]=%5d\n", i, candidates[i]);
    }

    // 各候補についてその選択のもとで解かせる
    for (int i=0;i<candidates.size();i++){

        printf(" 選択開始:candidates[%d](decisions=%d)=%d\n", i, decisions, candidates[i]);
        printf("   選択した変数=%d\n", candidates[i]);
        printf("   変数のインデックス=%d\n", i);

        // 今のタイミングまでの介入の情報を今のタイミングの選択部分(-2)を受け取った候補に変えた上でファイルに書き込む
        writeSubIntervention(candidates[i]);

        // 問題を解く
        execMinisat(prob, "sub-proof", "sub-intervention");

        // 解いた結果から必要な情報を出力する
        print_result("res");

        // drat-trimで証明を短くする
        execDrattrim(prob, "sub-proof", "sub-trimed-proof");

        // 証明の長さを測る
        int length = getProofLength("sub-trimed-proof");

        // 最良な変数を更新する
        if (min_length == -1 || length < min_length) {
            min_length = length;
            ret_i = i;
            ret = candidates[i];
        }
        printf("   証明の長さ=%d\n", length);
    }

    // 後の候補による変数選択の際での無駄な処理を防ぐため、今のタイミングでの選択(-2)を最良の変数として決定する
    assert(usr_picks[next_intervention] == -2);
    usr_picks[next_intervention] = ret;

    printf(" 各選択からの結果\n");
    printf("  証明が短くなった変数=%d\n", ret);
    printf("  変数のインデックス=%d\n", ret_i);
    printf("  証明の長さ=%d\n", min_length);

    printf("終了:selectFromCandidateVars()\n");
    
    return ret;
}

Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }
    
    // ユーザが自分で変数選択する場合(割り当て済みでも可能)(重みを書き換える場合の処理もここでやる予定)
    // usr_interbentionsの最後は-1だからそこを見ている限りはnext_interventionは増えない(エラーに行かない)
    assert(decisions>0);
    if (usr_interventions[next_intervention] == decisions) {
        // 選択する変数が既に決まっている場合
        if (usr_picks[next_intervention] != -2) {
            next = usr_picks[next_intervention];
        // 候補を決めてその中から選ぶ場合
        } else {
            next = selectFromCandidateVars();
        }
        next_intervention++;
    }
    

    // Activity based decision:
    // VMap<char> decision:変数が決定ヒューリスティックでの選択に適格(資格がある)かどうかを宣言してる(!decision[next]=資格がない)
    // 初期値は(int)1,(char)''('\0'ではないらしい) => 初期値は全て資格がある(変更してるとこはなさそう)
    // ※true=(int)1,(char)'', false=(int)0,(char)''
    while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()){ // 全部の変数への割り当てが決まった
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin(); // 削除した変数はcancelUntil()のinsertVarOrder()でやってる
    }

    // Choose polarity(極性) based on different polarity modes (global or per-variable):
    if (next == var_Undef){
        return lit_Undef;
    //　new_varかsetPolarityで設定されたリテラルの真偽がある場合はそれに従うが実際にそれを使ってる奴はなさそう
    } else if (user_pol[next] != l_Undef) {
        return mkLit(next, user_pol[next] == l_True);
    } else if (rnd_pol){
        return mkLit(next, drand(random_seed) < 0.5);
    } else { // オプション無しだと全部ここに行く
        // polarityは初期値は真でそれ以降は最新の割り当てを再び割り当ててそう(trailの結果を保存しておいてそれを使う)
        return mkLit(next, polarity[next]);
    }
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
    
    // このanalyzeで学習節を吐き出させたい(今はうまく行ってないかも)
    // printf("analyze\n");
    // for (int j = 0; j < out_learnt.size(); j++) {
    //         printf("%s%d ", (sign(out_learnt[j])? "-" : ""), var(out_learnt[j])+1); 
    // }
    // printf("0\n");
}


// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p)
{
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    Clause*               c     = &ca[reason(var(p))];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];
            
            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; }
            
            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }
                    
                return false;
            }

            // Recursively check 'l':
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[reason(var(p))];
        }else{
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }

            // Terminate with success if stack is empty:
            if (stack.size() == 0) break;
            
            // Continue with top element on stack:
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, LSet& out_conflict)
{
    out_conflict.clear();
    out_conflict.insert(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.insert(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}

// unchecked(検査を受けていない)
void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:(事後条件)
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    // printf("propagate()を実行します\n");
    CRef    confl     = CRef_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches.lookup(p);
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;
            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }
            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);
        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;
    // printf("propagate()を実行しました\n");
    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim)){
            // fprintf(proof_file, "Solver::reduceDB");
            removeClause(learnts[i]);
        }
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    string pre_clause;
    bool changed;
    for (i = j = 0; i < cs.size(); i++){
        if (false) {
            for (int k = 0; k < ca[cs[i]].size(); k++) {
                fprintf(proof_file, "%s%d ", (sign(ca[cs[i]][k])? "-" : ""), var(ca[cs[i]][k])+1);
            }
            fprintf(proof_file, "0->");
        }
        Clause& c = ca[cs[i]];
        if (proof_file) {
            pre_clause = "d ";
            changed = false;
            for (int l = 0; l < ca[cs[i]].size(); l++) {
                pre_clause += (sign(ca[cs[i]][l])? "-" : "") + to_string(var(ca[cs[i]][l])+1) + " ";
            }
            pre_clause = pre_clause + "0";
        }
        if (satisfied(c)){
            // fprintf(proof_file, "Solver::removeSatisfied");
            removeClause(cs[i]);
        }
        else{
            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                    // fprintf(proof_file, "del");
                    changed = true;
                }
            cs[j++] = cs[i];
            if (proof_file) {
                // pre_clauseとchangedが正しく機能しているかを見たい -> 機能してた
                for (int l = 0; l < ca[cs[i]].size(); l++) {
                    fprintf(proof_file, "%s%d ", (sign(ca[cs[i]][l])? "-" : ""), var(ca[cs[i]][l])+1);
                }
                fprintf(proof_file, "0\n");
                // fprintf(proof_file, "(changed=%s)\n", changed?"true":"false");
                if (changed) fprintf(proof_file, "%s\n", pre_clause.c_str());
            }
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
// !simplify()が成り立つ(つまりsimplify()=false)となるのはどんな時？
// => ソルバーをこの先動かしちゃいけない場合 or プロパゲーションで矛盾が起きた(矛盾が起きた節が返ってきた)場合
// Q.simplify()はeliminate()以外でも実行される？
//   A.実行される(test.cnfだと120回、-no-preで170回)
//   => 前処理をやると証明がおかしくなるのはsimplify()が原因ではなさそう
bool Solver::simplify()
{
    // printf(" Solver::simplify()を実行します\n");
    // printf("  nAssigns=%d(==?)simpDB_assigns=%d, simpDB_props=%d\n", nAssigns(), simpDB_assigns, simpDB_props);
    // assert(式):式を評価、真->何もしない
    //                    偽->メッセージボックスで情報を出力し、プログラムを終了させる
    assert(decisionLevel() == 0); // decisionLevel():trail_lim.size()を返す

    // okはソルバーをこの先動かしていいかみたいなもの？
    // Q.CRef_Undefは何を表している？
    //   A.端的に言えばNULL、CRef_Undefじゃなければ何かの節があるということ
    // ソルバーをこの先動かしちゃいけない場合
    //   or
    // プロパゲーションで矛盾が起きた(矛盾が起きた節が返ってきた)場合
    if (!ok || propagate() != CRef_Undef)
        return ok = false; // falseが返ってくるのはここだけ

    // simpDB_assignsの初期値は-1(変化しているかはわからない)
    // Q.simpDB_propsの値はpropagete()で変化していない？
    //   A.変化していない(simplify()では変化している)
    // printf("  nAssigns=%d(==?)simpDB_assigns=%d, simpDB_props=%d\n", nAssigns(), simpDB_assigns, simpDB_props);
    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    // printf("  learnts.size()=%d\n", learnts.size());
    // SimpSolver::eliminate()の実行時はlearnts.size()=0
    removeSatisfied(learnts);
    // printf("  remove_satisfied=%s\n", remove_satisfied? "true" : "false");
    // SimpSolver::eliminate()の実行時はremove_satisfied=false
    if (remove_satisfied){       // Can be turned off.
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?

        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0)
                trail[j++] = trail[i];
        trail.shrink(i - j);
        //printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
        qhead = trail.size();

        for (int i = 0; i < released_vars.size(); i++)
            seen[released_vars[i]] = 0;

        // Released variables are now ready to be reused:
        append(released_vars, free_vars);
        released_vars.clear();
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)
    // printf(" Solver::simplify()を実行しました\n");

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
// 実行は複数回される　
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0; // 矛盾回数の上限(上限に達したらリスタート) 
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            // analyzeとsearchのこの場所での学習節は一緒
            // => cancelUntilは節を削除したり書き換えたりしない
            // printf("search\n");
            // 証明部分
            if (proof_file) {
                for (int j = 0; j < learnt_clause.size(); j++) {
                    fprintf(proof_file, "%s%d ", (sign(learnt_clause[j])? "-" : ""), var(learnt_clause[j])+1); 
                }
                fprintf(proof_file, "0\n");
            }
            // ここで証明っぽいものを作ってみたがやっぱりダメ(8/10 12:21)
            // printf("%d\n", conflicts);
            // 学習節を作る回数と矛盾が起こる回数は同じ

            // decisionlevelを戻すのはこれより前で行う
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr); // 学習節の追加はここ
                attachClause(cr); // 監視リテラルの設定などを行う
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            // adjust(調整), cnt(count)
            // 矛盾が起きなかった段階で学習節の整理(reduceDB)をしてそう
            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    // %を出力したいときは%%と書く
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate(); // 上のprintfのところで使っている
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            // ユーザーが仮定を与えた場合それを１個づつとって確認する
            // とってくるリテラルはそれを真にするという仮定を表す(その時点で偽なら矛盾となりアウト)
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){ // 既に真なら何もしない(desicionlevelをあげないと無限ループになるのでそこ上げる)
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){ // 矛盾発生
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            // ユーザが与えた仮定を全て確認した場合(次に選ぶリテラルが決まってない)
            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(); // pickBranchLit()を使うのはここだけ

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite(有限な) subsequence(数列) that contains index 'x', and the
    // size of that subsequence:
    // ちょっと何やってるか不明(ちゃんと読めば分かりそうではある)
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
// 多分実行は一回だけ
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim)
        max_learnts = min_learnts_lim;

    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    // 変数が外側にあっても機能はするらしい
    // todo:FILE*  restore_fileを返す関数の作成(decisionLevel()みたいなもの)
    // printf("ccccc\n");
    // print_restore();
    // printf("aaaaa\n");
    // restore();
    while (status == l_Undef){
        // powは定義されている関数
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}


bool Solver::implies(const vec<Lit>& assumps, vec<Lit>& out)
{
    trail_lim.push(trail.size());
    for (int i = 0; i < assumps.size(); i++){
        Lit a = assumps[i];

        if (value(a) == l_False){
            cancelUntil(0);
            return false;
        }else if (value(a) == l_Undef)
            uncheckedEnqueue(a);
    }

    unsigned trail_before = trail.size();
    bool     ret          = true;
    if (propagate() == CRef_Undef){
        out.clear();
        for (int j = trail_before; j < trail.size(); j++)
            out.push(trail[j]);
    }else
        ret = false;
    
    cancelUntil(0);
    return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}

// print_restoreはしばらくはsolve_中のsearchの前においておく(解き始める直前)
// segmantation faultが起きるのはcloseしてないから？
// ファイルを受け取って書き込むより文字列を受け取ってオープン、書き込み、クローズまでやった方が良いのかも
void Solver::print_restore() {
    FILE* f = fopen("restore", "wb");
    // sizeof(int) = 4, sizeof(int64_t) = 8
    // fprintf(f, "int=%ld, int64_t=%ld\n", sizeof(int), sizeof(int64_t));
    // Extra results: (read-only member variable)
    //
    // vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    fprintf(f, "vec<lbool> model\n");
    fprintf(f, " Size sz %d\n", model.size());
    fprintf(f, " Size cap %d\n", model.capacity());
    fprintf(f, " lbool* data\n");
    for (int i = 0; i < model.size(); i++){
        fprintf(f, "  lbool data[%d]\n", i);
        fprintf(f, "   uint8_t value %u\n", model[i].get_value());
    }
    // LSet       conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    fprintf(f, "int verbosity %d\n", verbosity); // int       verbosity
    // FILE*     proof_file; 復元には必要ないので必要なさそう
    fprintf(f, "double var_decay %lf\n", var_decay); // double    var_decay;
    fprintf(f, "double clause_decay %lf\n", clause_decay); // double    clause_decay;
    fprintf(f, "double random_var_freq %lf\n", random_var_freq); // double    random_var_freq;
    fprintf(f, "double random_seed %lf\n", random_seed); // double    random_seed;
    fprintf(f, "bool luby_restart %s\n", (luby_restart ? "true" : "false")); // bool      luby_restart;
    fprintf(f, "int ccmin_mode %d\n", ccmin_mode); // int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    fprintf(f, "int phase_saving %d\n", phase_saving); // int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    fprintf(f, "bool rnd_pol %s\n", (rnd_pol ? "true" : "false")); // bool      rnd_pol;            // Use random polarities for branching heuristics.
    fprintf(f, "bool rnd_init_act %s\n", (rnd_init_act ? "true" : "false"));// bool      rnd_init_act;       // Initialize variable activities with a small random value.
    fprintf(f, "double garbage_frac %lf\n", garbage_frac); // double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.
    fprintf(f, "int min_learnts_lim %d\n", min_learnts_lim); // int       min_learnts_lim;    // Minimum number to set the learnts limit to.

    fprintf(f, "int restart_first %d\n", restart_first); // int       restart_first;      // The initial restart limit.                                                                (default 100)
    fprintf(f, "double restart_inc %lf\n", restart_inc); // double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    fprintf(f, "double learntsize_factor %lf\n", learntsize_factor); // double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    fprintf(f, "double learntsize_inc %lf\n", learntsize_inc); // double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    fprintf(f, "int learntsize_adjust_start_confl %d\n", learntsize_adjust_start_confl); // int       learntsize_adjust_start_confl;
    fprintf(f, "double learntsize_adjust_inc %lf\n", learntsize_adjust_inc); // double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    // uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    fprintf(f, "uint64_t solves %" PRIu64 "\n", solves);
    fprintf(f, "uint64_t starts %" PRIu64 "\n", starts);
    fprintf(f, "uint64_t decisions %" PRIu64 "\n", decisions);
    fprintf(f, "uint64_t rnd_decisions %" PRIu64 "\n", rnd_decisions);
    fprintf(f, "uint64_t propagations %" PRIu64 "\n", propagations);
    fprintf(f, "uint64_t conflicts %" PRIu64 "\n", conflicts);
    // uint64_t dec_vars, num_clauses, num_learnts, clauses_literals, learnts_literals, max_literals, tot_literals;
    fprintf(f, "uint64_t dec_vars %" PRIu64 "\n", dec_vars);
    fprintf(f, "uint64_t num_clauses %" PRIu64 "\n", num_clauses);
    fprintf(f, "uint64_t num_learnts %" PRIu64 "\n", num_learnts);
    fprintf(f, "uint64_t clauses_literals %" PRIu64 "\n", clauses_literals);
    fprintf(f, "uint64_t learnts_literals %" PRIu64 "\n", learnts_literals);
    fprintf(f, "uint64_t max_literals %" PRIu64 "\n", max_literals);
    fprintf(f, "uint64_t tot_literals %" PRIu64 "\n", tot_literals);



    // Helper structures:
    // 
    // struct VarData { CRef reason; int level; };
    // static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    // 構造体の中の関数宣言は実際に変数を定義するときに使う？
    // struct Watcher {
    //     CRef cref;
    //     Lit  blocker;
    //     Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
    //     bool operator==(const Watcher& w) const { return cref == w.cref; }
    //     bool operator!=(const Watcher& w) const { return cref != w.cref; }
    // };

    // operator()は"変数(引数)"で関数として呼び出しができる
    // struct WatcherDeleted
    // {
    //     const ClauseAllocator& ca;
    //     WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
    //    bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    // };

    // struct VarOrderLt {
    //     const IntMap<Var, double>&  activity;
    //     bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
    //     VarOrderLt(const IntMap<Var, double>&  act) : activity(act) { }
    // };

    // struct ShrinkStackElem {
    //     uint32_t i;
    //     Lit      l;
    //     ShrinkStackElem(uint32_t _i, Lit _l) : i(_i), l(_l){}
    // };
    // リテラルの出力
    // void print(FILE* f, char* name, int space){
    //     for (int i = 0; i < space; i++) fprintf(f, " "); fprintf(f, "Lit %s\n", name);
    //    for (int i = 0; i < space; i++) fprintf(f, " "); fprintf(f, " int x %d\n", x);
    // }

    // Solver state:
    //
    // vec<CRef>           clauses;          // List of problem clauses.
    fprintf(f, "vec<CRef> clauses\n");
    fprintf(f, " Size sz %d\n", clauses.size());
    fprintf(f, " Size cap %d\n", clauses.capacity());
    fprintf(f, " CRef* data\n");
    for (int i = 0; i < clauses.size(); i++){
        fprintf(f, "  CRef data[%d] %u\n", i, clauses[i]);
    }

    // vec<CRef>           learnts;          // List of learnt clauses.
    fprintf(f, "vec<CRef> learnts\n");
    fprintf(f, " Size sz %d\n", learnts.size());
    fprintf(f, " Size cap %d\n", learnts.capacity());
    fprintf(f, " CRef* data\n");
    for (int i = 0; i < learnts.size(); i++){
        fprintf(f, "  CRef data[%d] %u\n", i, learnts[i]);
    }
    // vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    fprintf(f, "vec<Lit> trail\n");
    fprintf(f, " Size sz %d\n", trail.size());
    fprintf(f, " Size cap %d\n", trail.capacity());
    fprintf(f, " Lit* data\n");
    for (int i = 0; i < trail.size(); i++){
        fprintf(f, "  Lit data[%d]\n", i);
        fprintf(f, "   int x %d\n", trail[i].x);
    }
    // vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    fprintf(f, "vec<int> trail_lim\n");
    fprintf(f, " Size sz %d\n", trail_lim.size());
    fprintf(f, " Size cap %d\n", trail_lim.capacity());
    fprintf(f, " int* data\n");
    for (int i = 0; i < trail_lim.size(); i++){
        fprintf(f, "  int data[%d] %d\n", i, trail_lim[i]);
    }
    // vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    fprintf(f, "vec<Lit> assumptions\n");
    fprintf(f, " Size sz %d\n", assumptions.size());
    fprintf(f, " Size cap %d\n", assumptions.capacity());
    fprintf(f, " Lit* data\n");
    for (int i = 0; i < assumptions.size(); i++){
        fprintf(f, "  Lit data[%d]\n", i);
        fprintf(f, "   int x %d\n", assumptions[i].x);
    }

    // VMap->IntMap
    // VMap<double>        activity;         // A heuristic measurement of the activity of a variable.
    fprintf(f, "VMap<double> activity\n");
    fprintf(f, " IntMap<Var, double>\n");
    fprintf(f, "  vec<double> map\n");
    fprintf(f, "   Size sz %d\n", activity.size());
    fprintf(f, "   Size cap %d\n", activity.capacity());
    fprintf(f, "   double* data\n");
    for (int i = 0; i < activity.size(); i++){
        fprintf(f, "    double data[%d] %lf\n", i, activity[i]);
    }
    // VMap<lbool>         assigns;          // The current assignments.
    fprintf(f, "VMap<lbool> assigns\n");
    fprintf(f, " IntMap<Var, lbool>\n");
    fprintf(f, "  vec<lbool> map\n");
    fprintf(f, "   Size sz %d\n", assigns.size());
    fprintf(f, "   Size cap %d\n", assigns.capacity());
    fprintf(f, "   lbool* data\n");
    for (int i = 0; i < assigns.size(); i++){
        fprintf(f, "    lbool data[%d]\n", i);
        fprintf(f, "     uint8_t value %u\n", assigns[i].get_value());
    }
    // VMap<char>          polarity;         // The preferred polarity of each variable.
    fprintf(f, "VMap<char> polarity\n");
    fprintf(f, " IntMap<Var, char>\n");
    fprintf(f, "  vec<char> map\n");
    fprintf(f, "   Size sz %d\n", polarity.size());
    fprintf(f, "   Size cap %d\n", polarity.capacity());
    fprintf(f, "   char* data\n");
    for (int i = 0; i < polarity.size(); i++){
        fprintf(f, "    char data[%d] %c\n", i, polarity[i]);
    }
    // VMap<lbool>         user_pol;         // The users preferred polarity of each variable.
    fprintf(f, "VMap<lbool> user_pol\n");
    fprintf(f, " IntMap<Var, lbool>\n");
    fprintf(f, "  vec<lbool> map\n");
    fprintf(f, "   Size sz %d\n", user_pol.size());
    fprintf(f, "   Size cap %d\n", user_pol.capacity());
    fprintf(f, "   lbool* data\n");
    for (int i = 0; i < user_pol.size(); i++){
        fprintf(f, "    lbool data[%d]\n", i);
        fprintf(f, "     uint8_t value %u\n", user_pol[i].get_value());
    }
    // VMap<char>          decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    fprintf(f, "VMap<char> decision\n");
    fprintf(f, " IntMap<Var, char>\n");
    fprintf(f, "  vec<char> map\n");
    fprintf(f, "   Size sz %d\n", decision.size());
    fprintf(f, "   Size cap %d\n", decision.capacity());
    fprintf(f, "   char* data\n");
    for (int i = 0; i < decision.size(); i++){
        fprintf(f, "    char data[%d] %c\n", i, decision[i]);
    }
    // VMap<VarData>       vardata;          // Stores reason and level for each variable.
    fprintf(f, "VMap<VarData> vardata\n");
    fprintf(f, " IntMap<Var, VarData>\n");
    fprintf(f, "  vec<VarData> map\n");
    fprintf(f, "   Size sz %d\n", vardata.size());
    fprintf(f, "   Size cap %d\n", vardata.capacity());
    fprintf(f, "   VarData* data\n");
    for (int i = 0; i < vardata.size(); i++){
        fprintf(f, "    VarData data[%d]\n", i);
        fprintf(f, "     CRef reason %u\n", vardata[i].reason);
        fprintf(f, "     int level %d\n", vardata[i].level);
    }
    // OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit> watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    fprintf(f, "OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit> watches\n");
    fprintf(f, " IntMap<Lit, vec<Watcher>, MkIndex> occs\n");
    fprintf(f, "  vec<vec<Watcher>> map\n");
    fprintf(f, "   Size sz %d\n", watches.occs.size());
    fprintf(f, "   Size cap %d\n", watches.occs.capacity());   
    fprintf(f, "   vec<Watcher>* data\n");
    for (int i = 0; i < watches.occs.size(); i++){
        fprintf(f, "    vec<Watcher> data[%d]\n", i);
        fprintf(f, "     Size sz %d\n", watches.occs.map.data[i].sz);
        fprintf(f, "     Size cap %d\n", watches.occs.map.data[i].cap);
        fprintf(f, "     Watcher* data\n");
        for (int j = 0; j < watches.occs.map.data[i].sz; j++){
            fprintf(f, "      Watcher data[%d]\n", j);
            fprintf(f, "       CRef cref %u\n", watches.occs.map.data[i].data[j].cref);
            fprintf(f, "       Lit blocker\n");
            fprintf(f, "        int x %d\n", watches.occs.map.data[i].data[j].blocker.x);
        }
    }
    fprintf(f, " IntMap<Lit, char, MkIndex> dirty\n");
    fprintf(f, "  vec<char> map\n");
    fprintf(f, "   Size sz %d\n", watches.dirty.size());
    fprintf(f, "   Size cap %d\n", watches.dirty.capacity());
    fprintf(f, "   char* data\n");
    for (int i = 0; i < watches.dirty.size(); i++){
        Lit l_i = mkLit(0, false);
        l_i.x = i;
        fprintf(f, "    char data[%d] %c\n", i, watches.dirty[l_i]);
    }
    fprintf(f, " vec<Lit> dirties\n");
    fprintf(f, "  Size sz %d\n", watches.dirties.size());
    fprintf(f, "  Size cap %d\n", watches.dirties.capacity());
    fprintf(f, "  Lit* data\n");
    for (int i = 0; i < watches.dirties.size(); i++){
        fprintf(f, "   Lit data[%d]\n", i);
        fprintf(f, "    int x %d\n", watches.dirties[i].x);
    }
    fprintf(f, " WatcherDeleted deleted\n");
    fprintf(f, "  ClauseAllocator& ca\n");
    fprintf(f, "   RegionAllocator<uint32_t> ra\n");
    fprintf(f, "    uint32_t* memory\n");
    fprintf(f, "    uint32_t sz %u\n", ca.ra.sz);
    fprintf(f, "    uint32_t cap %u\n", ca.ra.cap);
    for (uint32_t i = 0; i < ca.ra.sz; i++){
        fprintf(f, "     uint32_t memory[%u] %u\n", i, ca[i]);
    }
    fprintf(f, "    uint32_t wasted_ %u\n", ca.ra.wasted_);

    // Heap<Var,VarOrderLt>order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    fprintf(f, "Heap<Var,VarOrderLt> order_heap\n");
    fprintf(f, " vec<Var> heap\n");
    fprintf(f, "  Size sz %d\n", order_heap.heap.size());
    fprintf(f, "  Size cap %d\n", order_heap.heap.capacity());
    fprintf(f, "  Var* data\n");
    for (int i = 0; i < order_heap.heap.size(); i++){
        fprintf(f, "   Var data[%d] %d\n", i, order_heap.heap[i]);
    }
    fprintf(f, " IntMap<Var,int,MkIndex> indices\n");
    fprintf(f, "  vec<int> map\n");
    fprintf(f, "   Size sz %d\n", order_heap.indices.size());
    fprintf(f, "   Size cap %d\n", order_heap.indices.capacity());
    fprintf(f, "   int* data\n");
    for (int i = 0; i < order_heap.indices.size(); i++){
        fprintf(f, "    int data[%d] %d\n", i, order_heap.indices[i]);
    }
    fprintf(f, " VarOrderLt lt\n");
    fprintf(f, "  IntMap<Var, double>&  activity\n");
    fprintf(f, "   vec<double> map\n");
    fprintf(f, "    Size sz %d\n", order_heap.lt.activity.size());
    fprintf(f, "    Size cap %d\n", order_heap.lt.activity.capacity());
    fprintf(f, "    double* data\n");
    for (int i = 0; i < order_heap.lt.activity.size(); i++){
        fprintf(f, "     double data[%d] %lf\n", i, order_heap.lt.activity[i]);
    }

    fprintf(f, "bool ok %s\n", (ok ? "true" : "false")); // bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    fprintf(f, "double cla_inc %lf\n", cla_inc); // double              cla_inc;          // Amount to bump next clause with.
    fprintf(f, "double var_inc %lf\n", var_inc); // double              var_inc;          // Amount to bump next variable with.
    fprintf(f, "int qhead %d\n", qhead); // int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    fprintf(f, "int simpDB_assigns %d\n", simpDB_assigns); // int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    fprintf(f, "int64_t simpDB_props %" PRId64 "\n", simpDB_props); // int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    fprintf(f, "double progress_estimate %lf\n", progress_estimate); // double              progress_estimate;// Set by 'search()'.
    fprintf(f, "bool remove_satisfied %s\n", (remove_satisfied ? "true" : "false")); // bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    fprintf(f, "Var next_var %d\n", next_var); // Var                 next_var;         // Next variable to be created.
    // ClauseAllocator     ca;
    fprintf(f, "ClauseAllocator ca\n");
    fprintf(f, " RegionAllocator<uint32_t> ra\n");
    fprintf(f, "  uint32_t sz %u\n", ca.ra.sz);
    fprintf(f, "  uint32_t cap %u\n", ca.ra.cap);
    fprintf(f, "  uint32_t* memory\n");
    for (uint32_t i = 0; i < ca.ra.sz; i++){
        fprintf(f, "   uint32_t memory[%u] %u\n", i, ca[i]);
    }
    fprintf(f, "  uint32_t wasted_ %u\n", ca.ra.wasted_);

    // vec<Var>            released_vars;
    fprintf(f, "vec<Var> released_vars\n");
    fprintf(f, " Size sz %d\n", released_vars.size());
    fprintf(f, " Size cap %d\n", released_vars.capacity());
    fprintf(f, " Var* data\n");
    for (int i = 0; i < released_vars.size(); i++){
        fprintf(f, "  Var data[%d] %d\n", i, released_vars[i]);
    }
    // vec<Var>            free_vars;
    fprintf(f, "vec<Var> free_vars\n");
    fprintf(f, " Size sz %d\n", free_vars.size());
    fprintf(f, " Size cap %d\n", free_vars.capacity());
    fprintf(f, " Var* data\n");
    for (int i = 0; i < free_vars.size(); i++){
        fprintf(f, "  Var data[%d] %d\n", i, free_vars[i]);
    }

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    // VMap<char>          seen;
    fprintf(f, "VMap<char> seen\n");
    fprintf(f, " IntMap<Var, char>\n");
    fprintf(f, "  vec<char> map\n");
    fprintf(f, "   Size sz %d\n", seen.size());
    fprintf(f, "   Size cap %d\n", seen.capacity());
    fprintf(f, "   char* data\n");
    for (int i = 0; i < seen.size(); i++){
        fprintf(f, "    char data[%d] %c\n", i, seen[i]);
    }
    // vec<ShrinkStackElem>analyze_stack;
    fprintf(f, "vec<ShrinkStackElem> analyze_stack\n");
    fprintf(f, " Size sz %d\n", analyze_stack.size());
    fprintf(f, " Size cap %d\n", analyze_stack.capacity());
    fprintf(f, " ShrinkStackElem* data\n");
    for (int i = 0; i < analyze_stack.size(); i++){
        fprintf(f, "  ShrinkStackElem data[%d]\n", i);
        fprintf(f, "   uint32_t i %u\n", analyze_stack[i].i);
        fprintf(f, "   Lit l\n");
        fprintf(f, "    int x %d\n", analyze_stack[i].l.x);
    }
    // vec<Lit>            analyze_toclear;
    fprintf(f, "vec<Lit> analyze_toclear\n");
    fprintf(f, " Size sz %d\n", analyze_toclear.size());
    fprintf(f, " Size cap %d\n", analyze_toclear.capacity());
    fprintf(f, " Lit* data\n");
    for (int i = 0; i < analyze_toclear.size(); i++){
        fprintf(f, "  Lit data[%d]\n", i);
        fprintf(f, "   int x %d\n", analyze_toclear[i].x);
    }
    // vec<Lit>            add_tmp;
    fprintf(f, "vec<Lit> add_tmp\n");
    fprintf(f, " Size sz %d\n", add_tmp.size());
    fprintf(f, " Size cap %d\n", add_tmp.capacity());
    fprintf(f, " Lit* data\n");
    for (int i = 0; i < add_tmp.size(); i++){
        fprintf(f, "  Lit data[%d]\n", i);
        fprintf(f, "   int x %d\n", add_tmp[i].x);
    }

    fprintf(f, "double max_learnts %lf\n", max_learnts); // double              max_learnts;
    fprintf(f, "double learntsize_adjust_confl %lf\n", learntsize_adjust_confl); // double              learntsize_adjust_confl;
    fprintf(f, "int learntsize_adjust_cnt %d\n", learntsize_adjust_cnt); // int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    fprintf(f, "int64_t conflict_budget %" PRId64 "\n", conflict_budget); // int64_t             conflict_budget;    // -1 means no budget.
    fprintf(f, "int64_t propagation_budget %" PRId64 "\n", propagation_budget); // int64_t             propagation_budget; // -1 means no budget.
    fprintf(f, "bool asynch_interrupt %s\n", ( asynch_interrupt ? "true" : "false")); // bool                asynch_interrupt;
    fclose(f);
}

int N = 1000; // 文字列の長さの上限(2023/10/4時点では実際の文字列はmax64個程度)
// 文字列から先頭要素を取り除いて数値を文字列の状態で返す
char* Solver::getStrOfValue(FILE* f, char* prefix)
{
    char str[N]; // char* strにするとsegmentation errorになる(あらかじめサイズを指定しておかないといけない？)
    fgets(str, N, f);
    // printf("prefix=\"%s\" str=\"%s\"\n", prefix, str);
    if (strncmp(str,  prefix, strlen(prefix)) != 0) {printf("error:prefix=\"%s\" but str=\"%s\"\n", prefix, str);exit(1);}
    char* ret = (char*)malloc(sizeof(char) * N); int j = 0; //数値を入れる文字列配列と現在の書き込み位置
    for (int i = strlen(prefix); i < strlen(str)-1; i++) ret[j++] =  str[i]; ret[j] = '\0'; //数値の抽出
    return ret;
}

// 文字列型の数値を受け取ってuint64_t型の数値を返す
uint64_t Solver::stoui64(char* str) {
    uint64_t ret = 0;
    for (int i=0; str[i] != '\0'; i++) {
        ret *= 10;
        ret += (uint64_t)(str[i]-'0');
    }
    return ret;
}

// 文字列型の数値を受け取ってuint32_t型の数値を返す
uint32_t Solver::stoui32(char* str) {
    uint32_t ret = 0;
    for (int i=0; str[i] != '\0'; i++) {
        ret *= 10;
        ret += (uint32_t)(str[i]-'0');
    }
    return ret;
}

// 文字列型の数値を受け取ってint64_t型の数値を返す
int64_t Solver::stoi64(char* str) {
    int64_t ret = 0;
    for (int i=0; str[i] != '\0'; i++) {
        if (str[i] == '-') continue;
        ret *= 10;
        ret += (int64_t)(str[i]-'0');
    }
    if (str[0] == '-') ret *= -1;
    return ret;
}


void Solver::restore() {
    FILE* f = fopen("restore", "r");
    // fclose(f);
    // f = fopen("restore", "r");
    int sz;
    int cap;
    // ファイルの読み込みと復元
    // model
                                      getStrOfValue(f, "vec<lbool> model\n");
    model.sz                = atoi(   getStrOfValue(f, " Size sz "));
    model.cap               = atoi(   getStrOfValue(f, " Size cap "));
                                      getStrOfValue(f, " lbool* data\n");
    for (int i=0;i<model.sz;i++){
        char str[N];                      sprintf(str, "  lbool data[%d]\n", i); getStrOfValue(f, str);
        model.data[i].value = atoi(   getStrOfValue(f, "   uint8_t value "));;
    }
    verbosity                     = atoi(   getStrOfValue(f, "int verbosity "));
    var_decay                     = stod(   getStrOfValue(f, "double var_decay "));
    clause_decay                  = stod(   getStrOfValue(f, "double clause_decay "));
    random_var_freq               = stod(   getStrOfValue(f, "double random_var_freq "));
    random_seed                   = stod(   getStrOfValue(f, "double random_seed "));
    luby_restart                  =     (   getStrOfValue(f, "bool luby_restart ")[0] == 't') ? true : false; // 何故かstrcmpだと比較できず
    ccmin_mode                    = atoi(   getStrOfValue(f, "int ccmin_mode "));
    phase_saving                  = atoi(   getStrOfValue(f, "int phase_saving "));
    rnd_pol                       =     (   getStrOfValue(f, "bool rnd_pol ")[0] == 't') ? true : false;
    rnd_init_act                  =     (   getStrOfValue(f, "bool rnd_init_act ")[0] == 't') ? true : false;
    garbage_frac                  = stod(   getStrOfValue(f, "double garbage_frac "));
    min_learnts_lim               = atoi(   getStrOfValue(f, "int min_learnts_lim "));
    restart_first                 = atoi(   getStrOfValue(f, "int restart_first "));
    restart_inc                   = stod(   getStrOfValue(f, "double restart_inc "));
    learntsize_factor             = stod(   getStrOfValue(f, "double learntsize_factor "));
    learntsize_inc                = stod(   getStrOfValue(f, "double learntsize_inc "));
    learntsize_adjust_start_confl = atoi(   getStrOfValue(f, "int learntsize_adjust_start_confl "));
    learntsize_adjust_inc         = stod(   getStrOfValue(f, "double learntsize_adjust_inc "));
    solves                        = stoui64(getStrOfValue(f, "uint64_t solves "));
    starts                        = stoui64(getStrOfValue(f, "uint64_t starts "));
    decisions                     = stoui64(getStrOfValue(f, "uint64_t decisions "));
    rnd_decisions                 = stoui64(getStrOfValue(f, "uint64_t rnd_decisions "));
    propagations                  = stoui64(getStrOfValue(f, "uint64_t propagations "));
    conflicts                     = stoui64(getStrOfValue(f, "uint64_t conflicts "));
    dec_vars                      = stoui64(getStrOfValue(f, "uint64_t dec_vars "));
    num_clauses                   = stoui64(getStrOfValue(f, "uint64_t num_clauses "));
    num_learnts                   = stoui64(getStrOfValue(f, "uint64_t num_learnts "));
    clauses_literals              = stoui64(getStrOfValue(f, "uint64_t clauses_literals "));
    learnts_literals              = stoui64(getStrOfValue(f, "uint64_t learnts_literals "));
    max_literals                  = stoui64(getStrOfValue(f, "uint64_t max_literals "));
    tot_literals                  = stoui64(getStrOfValue(f, "uint64_t tot_literals "));
    // clauses
                                  getStrOfValue(f, "vec<CRef> clauses\n");
    clauses.sz          = atoi(   getStrOfValue(f, " Size sz "));
    clauses.cap         = atoi(   getStrOfValue(f, " Size cap "));
                                  getStrOfValue(f, " CRef* data\n");
    for (int i=0;i<clauses.sz;i++){
        char str[N];                  sprintf(str, "  CRef data[%d] ", i);
        clauses.data[i] = stoui32(getStrOfValue(f, str));;
    }
    // learnts
                                  getStrOfValue(f, "vec<CRef> learnts\n");
    learnts.sz          = atoi(   getStrOfValue(f, " Size sz "));
    learnts.cap         = atoi(   getStrOfValue(f, " Size cap "));
                                  getStrOfValue(f, " CRef* data\n");
    for (int i=0;i<learnts.sz;i++){
        char str[N];                  sprintf(str, "  CRef data[%d] ", i);
        learnts.data[i] = stoui32(getStrOfValue(f, str));;
    }
    // trail
                                            getStrOfValue(f, "vec<Lit> trail\n");
    trail.sz                      = atoi(   getStrOfValue(f, " Size sz "));
    trail.cap                     = atoi(   getStrOfValue(f, " Size cap "));
                                            getStrOfValue(f, " Lit* data\n");
    for (int i=0;i<trail.sz;i++){
        char str[N];                            sprintf(str, "  Lit data[%d]\n", i); getStrOfValue(f, str);
        trail[i].x                = atoi(   getStrOfValue(f, "   int x "));
    }
    // trail_lim
                                            getStrOfValue(f, "vec<int> trail_lim\n");
    trail_lim.sz                  = atoi(   getStrOfValue(f, " Size sz "));
    trail_lim.cap                 = atoi(   getStrOfValue(f, " Size cap "));
                                            getStrOfValue(f, " int* data\n");
    for (int i=0;i<trail_lim.sz;i++){
        char str[N];                            sprintf(str, "  int data[%d] ", i);
        trail_lim[i]              = atoi(   getStrOfValue(f, str));
    }
    // assumptions
                                            getStrOfValue(f, "vec<Lit> assumptions\n");
    assumptions.sz                = atoi(   getStrOfValue(f, " Size sz "));
    assumptions.cap               = atoi(   getStrOfValue(f, " Size cap "));
                                            getStrOfValue(f, " Lit* data\n");
    for (int i=0;i<assumptions.sz;i++){
        char str[N];                            sprintf(str, "  Lit data[%d]\n", i); getStrOfValue(f, str);
        assumptions[i].x          = atoi(   getStrOfValue(f, "   int x "));
    }
    // activity
                                            getStrOfValue(f, "VMap<double> activity\n");
                                            getStrOfValue(f, " IntMap<Var, double>\n");
                                            getStrOfValue(f, "  vec<double> map\n");
    activity.map.sz               = atoi(   getStrOfValue(f, "   Size sz "));
    activity.map.cap              = atoi(   getStrOfValue(f, "   Size cap "));
                                            getStrOfValue(f, "   double* data\n");
    for (int i=0;i<activity.map.sz;i++){
        char str[N];                            sprintf(str, "    double data[%d] ", i);
        activity[i]               = stod(   getStrOfValue(f, str));
    }
    // assigns
                                            getStrOfValue(f, "VMap<lbool> assigns\n");
                                            getStrOfValue(f, " IntMap<Var, lbool>\n");
                                            getStrOfValue(f, "  vec<lbool> map\n");
    assigns.map.sz                = atoi(   getStrOfValue(f, "   Size sz "));
    assigns.map.cap               = atoi(   getStrOfValue(f, "   Size cap "));
                                            getStrOfValue(f, "   lbool* data\n");
    for (int i=0;i<assigns.map.sz;i++){
        char str[N];                            sprintf(str, "    lbool data[%d]\n", i); getStrOfValue(f, str);
        assigns.map.data[i].value = atoi(   getStrOfValue(f, "     uint8_t value "));;
    }
    // polarity
                            getStrOfValue(f, "VMap<char> polarity\n");
                            getStrOfValue(f, " IntMap<Var, char>\n");
                            getStrOfValue(f, "  vec<char> map\n");
    polarity.map.sz  = atoi(getStrOfValue(f, "   Size sz "));
    polarity.map.cap = atoi(getStrOfValue(f, "   Size cap "));
                            getStrOfValue(f, "   char* data\n");
    for (int i=0;i<polarity.map.sz;i++){
        char str[N];            sprintf(str, "    char data[%d] ", i);
        polarity[i]  =      getStrOfValue(f, str)[0];
    }
    // user_pol
                                             getStrOfValue(f, "VMap<lbool> user_pol\n");
                                             getStrOfValue(f, " IntMap<Var, lbool>\n");
                                             getStrOfValue(f, "  vec<lbool> map\n");
    user_pol.map.sz                = atoi(   getStrOfValue(f, "   Size sz "));
    user_pol.map.cap               = atoi(   getStrOfValue(f, "   Size cap "));
                                             getStrOfValue(f, "   lbool* data\n");
    for (int i=0;i<user_pol.map.sz;i++){
        char str[N];                             sprintf(str, "    lbool data[%d]\n", i); getStrOfValue(f, str);
        user_pol.map.data[i].value = atoi(   getStrOfValue(f, "     uint8_t value "));
    }
    // decision
                                            getStrOfValue(f, "VMap<char> decision\n");
                                            getStrOfValue(f, " IntMap<Var, char>\n");
                                            getStrOfValue(f, "  vec<char> map\n");
    decision.map.sz               = atoi(   getStrOfValue(f, "   Size sz "));
    decision.map.cap              = atoi(   getStrOfValue(f, "   Size cap "));
                                            getStrOfValue(f, "   char* data\n");
    for (int i=0;i<decision.map.sz;i++){
        char str[N];                            sprintf(str, "    char data[%d] ", i);
        decision[i]               =         getStrOfValue(f, str)[0];
    }
    // vardata
                                             getStrOfValue(f, "VMap<VarData> vardata\n");
                                             getStrOfValue(f, " IntMap<Var, VarData>\n");
                                             getStrOfValue(f, "  vec<VarData> map\n");
    vardata.map.sz                 = atoi(   getStrOfValue(f, "   Size sz "));
    vardata.map.cap                = atoi(   getStrOfValue(f, "   Size cap "));
                                             getStrOfValue(f, "   VarData* data\n");
    for (int i=0;i<vardata.map.sz;i++){
        char str[N];                             sprintf(str, "    VarData data[%d]\n", i); getStrOfValue(f, str);
        vardata.map.data[i].reason = atoi(   getStrOfValue(f, "     CRef reason "));
        vardata.map.data[i].level  = atoi(   getStrOfValue(f, "     int level "));
    }
    // watches
                                               getStrOfValue(f, "OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit> watches\n");
                                               getStrOfValue(f, " IntMap<Lit, vec<Watcher>, MkIndex> occs\n");
                                               getStrOfValue(f, "  vec<vec<Watcher>> map\n");
    sz = atoi(   getStrOfValue(f, "   Size sz "));
    cap = atoi(   getStrOfValue(f, "   Size cap "));
                                               getStrOfValue(f, "   vec<Watcher>* data\n");
    for (int i=0;i<watches.occs.map.sz;i++){
        char str[N];                               sprintf(str, "    vec<Watcher> data[%d]\n", i); getStrOfValue(f, str);
        watches.occs.map.data[i].sz  = atoi(   getStrOfValue(f, "     Size sz "));
        watches.occs.map.data[i].cap = atoi(   getStrOfValue(f, "     Size cap "));
                                               getStrOfValue(f, "     Watcher* data\n");
        for (int j=0;j<watches.occs.map.data[i].sz;j++){
            char str[N];                           sprintf(str, "      Watcher data[%d]\n", j); getStrOfValue(f, str);
            watches.occs.map.data[i].data[j].cref =
                                       atoi(   getStrOfValue(f, "       CRef cref "));
                                                   sprintf(str, "       Lit blocker\n"); getStrOfValue(f, str);
            watches.occs.map.data[i].data[j].blocker.x =
                                       atoi(   getStrOfValue(f, "        int x "));
        }
    }
                                               getStrOfValue(f, " IntMap<Lit, char, MkIndex> dirty\n");
                                               getStrOfValue(f, "  vec<char> map\n");
    watches.dirty.map.sz             = atoi(   getStrOfValue(f, "   Size sz "));
    watches.dirty.map.cap            = atoi(   getStrOfValue(f, "   Size cap "));
                                               getStrOfValue(f, "   char* data\n");
    for (int i=0;i<watches.dirty.map.sz;i++){
        char str[N];                               sprintf(str, "    char data[%d] ", i);
        watches.dirty.map.data[i]   =          getStrOfValue(f, str);
    }
                                               getStrOfValue(f, " vec<Lit> dirties\n");
    watches.dirties.sz               = atoi(   getStrOfValue(f, "  Size sz "));
    watches.dirties.cap              = atoi(   getStrOfValue(f, "  Size cap "));
        
                                               getStrOfValue(f, "  Lit* data\n");
    for (int i=0;i<watches.dirties.sz;i++){
        char str[N];                               sprintf(str, "   Lit data[%d]\n", i); getStrOfValue(f, str);
        watches.dirties[i].x         = atoi(   getStrOfValue(f, "    int x "));
    }
                                               getStrOfValue(f, " WatcherDeleted deleted\n");
                                               getStrOfValue(f, "  ClauseAllocator& ca\n");
                                               getStrOfValue(f, "   RegionAllocator<uint32_t> ra\n");
                                               getStrOfValue(f, "    uint32_t* memory\n");
    watches.deleted.ca.ra.sz         = stoui32(getStrOfValue(f, "    uint32_t sz "));
    watches.deleted.ca.ra.cap        = stoui32(getStrOfValue(f, "    uint32_t cap "));
    for (uint32_t i=0;i<watches.deleted.ca.ra.sz;i++) {
        char str[N];                               sprintf(str, "     uint32_t memory[%u] ", i);
        watches.deleted.ca.ra.memory[i] = stoui32(getStrOfValue(f, str));
    }
    watches.deleted.ca.ra.wasted_    = stoui32(getStrOfValue(f, "    uint32_t wasted_ "));
    // order_heap
                                                     getStrOfValue(f, "Heap<Var,VarOrderLt> order_heap");
                                                     getStrOfValue(f, " vec<Var> heap\n");
    order_heap.heap.sz                     = atoi(   getStrOfValue(f, "  Size sz "));
    order_heap.heap.cap                    = atoi(   getStrOfValue(f, "  Size cap "));
    
                                                     getStrOfValue(f, "  Var* data\n");
    for (int i=0;i<order_heap.heap.sz;i++){
        char str[N];                                     sprintf(str, "   Var data[%d] ", i);
        order_heap.heap.data[i]            = atoi(   getStrOfValue(f, str));
    }
                                                     getStrOfValue(f, " IntMap<Var,int,MkIndex> indices\n");
                                                     getStrOfValue(f, "  vec<int> map\n");
    sz                                     = atoi(   getStrOfValue(f, "   Size sz ")); order_heap.indices.map.growTo(sz);
    cap                                    = atoi(   getStrOfValue(f, "   Size cap ")); order_heap.indices.map.capacity(cap);
    
                                                     getStrOfValue(f, "   int* data\n");
    for (int i=0;i<order_heap.indices.map.sz;i++){
        char str[N];                                     sprintf(str, "    int data[%d] ", i);
        order_heap.indices.map.data[i]     = atoi(   getStrOfValue(f, str));
    }
                                                     getStrOfValue(f, " VarOrderLt lt\n");
                                                     getStrOfValue(f, "  IntMap<Var, double>&  activity\n");
                                                     getStrOfValue(f, "   vec<double> map\n");
    sz                                     = atoi(   getStrOfValue(f, "    Size sz ")); order_heap.lt.activity.map.growTo(sz);
    cap                                    = atoi(   getStrOfValue(f, "    Size cap ")); order_heap.lt.activity.map.capacity(cap);
                                                     getStrOfValue(f, "    double* data\n");
    for (int i=0;i<order_heap.lt.activity.map.sz;i++){
        char str[N];                                     sprintf(str, "     double data[%d] ", i);
        order_heap.lt.activity.map.data[i] = stod(   getStrOfValue(f, str));
    }
    // ok ~ next_var
    ok                =     (  getStrOfValue(f, "bool ok ")[0] == 't') ? true : false;
    cla_inc           = stod(  getStrOfValue(f, "double cla_inc "));
    var_inc           = stod(  getStrOfValue(f, "double var_inc "));
    qhead             = atoi(  getStrOfValue(f, "int qhead "));
    simpDB_assigns    = atoi(  getStrOfValue(f, "int simpDB_assigns "));
    simpDB_props      = stoi64(getStrOfValue(f, "int64_t simpDB_props "));
    progress_estimate = stod(  getStrOfValue(f, "double progress_estimate "));
    remove_satisfied  =     (  getStrOfValue(f, "bool remove_satisfied ")[0] == 't') ? true : false;
    next_var          = atoi(  getStrOfValue(f, "Var next_var "));
    // ca
                                  getStrOfValue(f, "ClauseAllocator ca\n");
                                  getStrOfValue(f, " RegionAllocator<uint32_t> ra\n");
    ca.ra.sz            = stoui32(getStrOfValue(f, "  uint32_t sz "));
    ca.ra.cap           = stoui32(getStrOfValue(f, "  uint32_t cap "));
                                  getStrOfValue(f, "  uint32_t* memory\n");
    for (uint32_t i=0;i<ca.ra.sz;i++) {
        char str[N];                  sprintf(str, "   uint32_t memory[%u] ", i);
        ca.ra.memory[i] = stoui32(getStrOfValue(f, str));
    }
    ca.ra.wasted_       = stoui32(getStrOfValue(f, "  uint32_t wasted_ "));
    // released_vars
                                        getStrOfValue(f, "vec<Var> released_vars\n");
    sz                        = atoi(   getStrOfValue(f, " Size sz ")); released_vars.growTo(sz);
    cap                       = atoi(   getStrOfValue(f, " Size cap ")); released_vars.capacity(cap);
    
                                        getStrOfValue(f, " Var* data\n");
    for (int i=0;i<released_vars.sz;i++){
        char str[N];                        sprintf(str, "  Var data[%d]", i);
        released_vars.data[i] = atoi(   getStrOfValue(f, str));
    }

                                    getStrOfValue(f, "vec<Var> free_vars\n");
    sz                    = atoi(   getStrOfValue(f, " Size sz ")); free_vars.growTo(sz);
    cap                   = atoi(   getStrOfValue(f, " Size cap ")); free_vars.capacity(cap);
     
                                    getStrOfValue(f, " Var* data\n");
    for (int i=0;i<free_vars.sz;i++){
        char str[N];                    sprintf(str, "  Var data[%d]", i);
        free_vars.data[i] = atoi(   getStrOfValue(f, str));
    }
    // seen
                                        getStrOfValue(f, "VMap<char> seen\n");
                                        getStrOfValue(f, " IntMap<Var, char>\n");
                                        getStrOfValue(f, "  vec<char> map\n");
    sz                        = atoi(   getStrOfValue(f, "   Size sz ")); seen.map.growTo(sz);
    cap                       = atoi(   getStrOfValue(f, "   Size cap ")); seen.map.capacity(cap);    
                                        getStrOfValue(f, "   char* data\n");
    for (int i=0;i<seen.map.sz;i++){
        char str[N];                        sprintf(str, "    char data[%d] ", i);
        seen.map.data[i]      =         getStrOfValue(f, str)[0];
    }
    // analyze_stack
                                            getStrOfValue(f, "vec<ShrinkStackElem> analyze_stack\n");
    sz                            = atoi(   getStrOfValue(f, " Size sz ")); analyze_stack.sz = sz;
    cap                           = atoi(   getStrOfValue(f, " Size cap ")); analyze_stack.cap = cap;    
                                            getStrOfValue(f, " ShrinkStackElem* data\n");
    for (int i=0;i<analyze_stack.sz;i++) {
        char str[N];                            sprintf(str, "  ShrinkStackElem data[%d]\n", i);
                                            getStrOfValue(f, str);
        analyze_stack.data[i].i   = stoui32(getStrOfValue(f, "   uint32_t i "));
                                            getStrOfValue(f, "   Lit l\n");
        analyze_stack.data[i].l.x =    atoi(getStrOfValue(f, "    int x "));
    }
    // analze_toclear
                                            getStrOfValue(f, "vec<Lit> analyze_toclear\n");
    sz                            = atoi(   getStrOfValue(f, " Size sz ")); analyze_toclear.growTo(sz);
    cap                           = atoi(   getStrOfValue(f, " Size cap ")); analyze_toclear.capacity(cap);
                                            getStrOfValue(f, " Lit* data\n");
    for (int i=0;i<analyze_toclear.sz;i++){
        char str[N];                            sprintf(str, "  Lit data[%d]\n", i); getStrOfValue(f, str);
        analyze_toclear.data[i].x = atoi(   getStrOfValue(f, "   int x "));
    }
    // add_tmp
                                    getStrOfValue(f, "vec<Lit> add_tmp\n");
    sz                    = atoi(   getStrOfValue(f, " Size sz ")); add_tmp.growTo(sz);
    cap                   = atoi(   getStrOfValue(f, " Size cap ")); add_tmp.capacity(cap);
                                    getStrOfValue(f, " Lit* data\n");
    for (int i=0;i<add_tmp.sz;i++){
        char str[N];                    sprintf(str, "  Lit data[%d]\n", i); getStrOfValue(f, str);
        add_tmp.data[i].x = atoi(   getStrOfValue(f, "   int x "));
    }
    max_learnts             = stod(  getStrOfValue(f, "double max_learnts "));
    learntsize_adjust_confl = stod(  getStrOfValue(f, "double learntsize_adjust_confl "));
    learntsize_adjust_cnt   = atoi(  getStrOfValue(f, "int learntsize_adjust_cnt "));
    conflict_budget         = stoi64(getStrOfValue(f, "int64_t conflict_budget "));
    propagation_budget      = stoi64(getStrOfValue(f, "int64_t propagation_budget "));
    asynch_interrupt        =     (  getStrOfValue(f, "bool asynch_interrupt ")[0] == 't') ? true : false;


    
    


    // あとまわし
    // fprintf(f, "int64_t simpDB_props %" PRId64 "\n", simpDB_props); // int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.

    


                            


   




    

    fclose(f);
}

void Solver::printStats() const
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
        // 'dangling' reasons here. It is safe and does not hurt.
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            ca.reloc(learnts[i], to);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
