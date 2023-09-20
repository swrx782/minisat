/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

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

#include <errno.h>
#include <zlib.h>

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/simp/SimpSolver.h"

using namespace Minisat;

//=================================================================================================


static Solver* solver;
// Terminate by notifying the solver and back out(取り消す、破棄する) gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int) { solver->interrupt(); } // プロトタイプ宣言？でも定義はしてる

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
// deadlocks(デッドロック):複数の実行中のプログラムなどが互いに他のプログラムの結果待ちとなり、待機状態に入ったまま動かなくなる現象
static void SIGINT_exit(int) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        // printf("solver->verbosity=%d \n", solver->verbosity);
        // minisatで実行してすぐCtrl+cだと1になる
        // ファイル(10094.cnf)指定して途中でCtrl+cしてもINTERRUPTED ***が出てこない
        //   =>この関数を呼び出してなさそう
        solver->printStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
    try {
        // ファイル指定されてなくても実行はしてるっぽい(printfが実行されている)
        // setUsageHelpは--help、--help-verbの時に実行されてるっぽい
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        setX86FPUPrecision();
        
        // Extra options:
        //
        // 引数の文字列は--help,--help-verbで出力されている
        // 第一引数は--help,--help-verbの出力の際の種別(CORE,MAIN,SIMP,...)を指定している？
        // 第一引数をMAINからCOREにすると種別は変わっている
        // 第二引数=オプション名？
        // 第三引数=--help-verbでの詳細説明？
        // 第四引数=デフォルト値
        // 第五引数=オプションで指定できる範囲？
        // 型はutils/options.hで定義
        // verbosity(冗長性)
        // verbは探索の際の各結果(矛盾の数や学習節の数)をどれくらい詳細に出力するかを決める
        // 0だとなし、2にするとガーベジコレクションの情報とかも出力される
        // 毎回オプション指定が面倒ならここで指定できそう
        // 証明を吐かせるかどうかの変数はS.verbosityで
        IntOption    verb   ("MIAN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        // -no-preで209.cnf,test.cnfを解かせると正しい証明になる
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        BoolOption   solve  ("MAIN", "solve",  "Completely turn on/off solving after preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);
        // 証明を吐かせるかどうかのオプション
        // 節を作るたびに吐かせているのでUNSATでない場合も証明の書き込みを行う
        StringOption proof ("MAIN", "proof", "If given, write the proof to this file(proof=column of lemmas).");

        // オプション引数の解析(どこまでやってるかは後で確認)
        parseOptions(argc, argv, true); // -> utils/Option.h -> utils/Options.cc
        // オプション指定はできた
        // printf("dimacs=%s\n", (dimacs)?"true":"false");
        // proofを指定しない場合NULLでもない何らかの値が入る
        // printf("proof=%s\n", proof);
        
        SimpSolver  S; // -> simp/SimpSolver.h -> core/Solver.cc
        double      initial_time = cpuTime(); // 

        // 簡約化のようなことをしている(おそらく節の削除をしてる、変数を削除しているかは不明)
        // ファイルを読んでもいないのに何を簡約化をしている？
        // -no-pre,-no-pre test.cnf でやるとtrueが返ってくる
        if (!pre) S.eliminate(true); // -> simp/SimpSolver.h -> simp/SimpSolver.cc


        // verbostiyは探索の際の各結果(矛盾の数や学習節の数)をどれくらい詳細に出力するかを決める
        // 0だとなし、2にするとガーベジコレクションの情報とかも出力される
        S.verbosity = verb;
        // 問題指定しなくてもここまではやってる
        // proofは指定しなかった時はNULLになっている
        // 現時点ではS.proof_fileにはSolver.ccで指定した値("")が入っているはず
        // printf("S.proof_file=%s\n", S.proof_file);
        // wb:長さ0にするか、新しいバイナリファイルを作って書き込む
        // => 元からファイルに書かれていた内容は消える
        // ファイルオープンに失敗した場合は証明を書き込まずに問題を解き続けることに注意
        S.proof_file = (proof)? fopen(proof, "wb") : NULL;
        // S.proof_fileにはproofを指定すれば指定した値、指定しなければNULLが入る
        // printf("-> S.proof_file=%s\n", S.proof_file);
        // printf("S.proof_file==NULL?=%s\n", S.proof_file==NULL?"true":"false");
        // S.proof_fileがNULLの場合にfprintfをしようとするとエラーが起きるので注意
        // if (S.proof_file) fprintf(S.proof_file, "cpuTime()=%f\n", cpuTime());
        // if (S.proof_file) fprintf(S.proof_file, "cpuTime()=%f\n", cpuTime());

        
        solver = &S;
        // 各変数はsolver->変数名で参照可能
        
        // 関数sigTermによってCtrl+cで抜ける時の処理を設定している
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        sigTerm(SIGINT_exit);

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);

        if (argc == 1)
            // printf("こっちはsimp/main"); 実行ではこっちを使ってるっぽい
            // simpはsimpleじゃなくsimplification？
            printf("Reading from standard input... Use '--help' for help.\n");

        // gzopen:gzipファイルをオープンする("rb"=読み込み)
        // gzipフォーマットでないファイルの読み込みについても使用することができるらしい
        // argv[1] = ファイル名
        //　第一引数を0にするとどうなる？
        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n"); }
        
        // ファイル名を指定しないとparse_DIMACS(StreamBuffer)が終わらないっぽい
        // parse_DIMACSを見ながら節がどのように格納されているか見る(8/7)
        // printf("nassigns=%d\n", S.nAssigns());
        // nAssignsが変わるのはここ
        parse_DIMACS(in, S, (bool)strictp); // -> core/Dimacs.h
        gzclose(in);
        // printf("nassigns=%d\n", S.nAssigns());
        // printf("parse_DIMACS()を実行しました\n");
        // res:結果(SAT,UNSAT)を出力するファイル
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        sigTerm(SIGINT_interrupt);

        //                 =>そもそもparse_DIMACSで止まる
        //         test.cnf=>trueが返る
        // -no-pre         =>そもそもparse_DIMACSで止まる
        // -no-pre test.cnf=>trueが返る
        // printf("実行開始:S.eliminate()\n");
        S.eliminate(true);
        // printf("実行終了:S.eliminate()\n");
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
            printf("|                                                                             |\n"); }

        // 簡約化をした時点でUNSATなら結果を出力して終了する
        // S.printStats()はrestarts,conflicts,...,CPU timeなどのソルバーの状態を出力する
        if (!S.okay()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by simplification\n");
                S.printStats();
                printf("\n"); }
            printf("UNSATISFIABLE\n");
            exit(20);
        }

        // l_Undef,retは何を表している？
        // retは戻り値？(retun)
        // lboolはリテラルの状態を表す型(真、偽、未定義)
        lbool ret = l_Undef; // -> core/SolverTypes.h

        // solveは前処理をした後に問題を解くかどうか
        if (solve){
            vec<Lit> dummy;
            // 仮定(dummyなので空？)を加えて問題を解く。つまりここを見れば良さそう
            ret = S.solveLimited(dummy); // -> simp/SimpSolver.h
        }else if (S.verbosity > 0)
            printf("===============================================================================\n");

        if (dimacs && ret == l_Undef)
            S.toDimacs((const char*)dimacs);

        if (S.verbosity > 0){
            S.printStats();
            printf("\n"); }
        printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        if (res != NULL){
            if (ret == l_True){
                fprintf(res, "SAT\n");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }else if (ret == l_False)
                fprintf(res, "UNSAT\n");
            else
                fprintf(res, "INDET\n");
            fclose(res);
        }

#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
