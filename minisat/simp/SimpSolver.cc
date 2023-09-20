/***********************************************************************************[SimpSolver.cc]
Copyright (c) 2006,      Niklas Een, Niklas Sorensson
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

#include "minisat/mtl/Sort.h"
#include "minisat/simp/SimpSolver.h"
#include "minisat/utils/System.h"

#include<string>

using namespace Minisat;

using namespace std;

//=================================================================================================
// Options:


static const char* _cat = "SIMP";

static BoolOption   opt_use_asymm        (_cat, "asymm",        "Shrink clauses by asymmetric branching.", false);
static BoolOption   opt_use_rcheck       (_cat, "rcheck",       "Check if a clause is already implied. (costly)", false);
static BoolOption   opt_use_elim         (_cat, "elim",         "Perform variable elimination.", true);
static IntOption    opt_grow             (_cat, "grow",         "Allow a variable elimination step to grow by a number of clauses.", 0);
static IntOption    opt_clause_lim       (_cat, "cl-lim",       "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit", 20,   IntRange(-1, INT32_MAX));
static IntOption    opt_subsumption_lim  (_cat, "sub-lim",      "Do not check if subsumption against a clause larger than this. -1 means no limit.", 1000, IntRange(-1, INT32_MAX));
static DoubleOption opt_simp_garbage_frac(_cat, "simp-gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered during simplification.",  0.5, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    grow               (opt_grow)
  , clause_lim         (opt_clause_lim)
  , subsumption_lim    (opt_subsumption_lim)
  , simp_garbage_frac  (opt_simp_garbage_frac)
  , use_asymm          (opt_use_asymm)
  , use_rcheck         (opt_use_rcheck)
  , use_elim           (opt_use_elim)
  , extend_model       (true)
  , merges             (0)
  , asymm_lits         (0)
  , eliminated_vars    (0)
  , elimorder          (1)
  , use_simplification (true)
  , occurs             (ClauseDeleted(ca))
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
  , n_touched          (0)
{
    vec<Lit> dummy(1,lit_Undef);
    ca.extra_clause_field = true; // NOTE: must happen before allocating the dummy clause below.
    bwdsub_tmpunit        = ca.alloc(dummy);
    remove_satisfied      = false;
}


SimpSolver::~SimpSolver()
{
}


Var SimpSolver::newVar(lbool upol, bool dvar) {
    Var v = Solver::newVar(upol, dvar);

    frozen    .insert(v, (char)false);
    eliminated.insert(v, (char)false);

    if (use_simplification){
        n_occ     .insert( mkLit(v), 0);
        n_occ     .insert(~mkLit(v), 0);
        occurs    .init  (v);
        touched   .insert(v, 0);
        elim_heap .insert(v);
    }
    return v; }


void SimpSolver::releaseVar(Lit l)
{
    assert(!isEliminated(var(l)));
    if (!use_simplification && var(l) >= max_simp_var)
        // Note: Guarantees that no references to this variable is
        // left in model extension datastructure. Could be improved!
        Solver::releaseVar(l);
    else
        // Otherwise, don't allow variable to be reused.
        Solver::addClause(l);
}


lbool SimpSolver::solve_(bool do_simp, bool turn_off_simp)
{
    vec<Var> extra_frozen;
    lbool    result = l_True;

    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }

    if (result == l_True)
        result = Solver::solve_();
    else if (verbosity >= 1)
        printf("===============================================================================\n");

    if (result == l_True && extend_model)
        extendModel();

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}



// SolverのaddClauseには無いものがあるはず
// 簡約とかの情報が入ってる可能性があるんじゃないか(n_touchedとか)
// 問題を読み込む際にSimpSolver::addClause_()は問題の節の数だけ実行される
bool SimpSolver::addClause_(vec<Lit>& ps)
{
    // printf("実行開始:SimpSolver::addClause_()\n");
    if (false) {
        printf(" ps= ");
        for (int j = 0; j < ps.size(); j++) {
            printf("%s%d ", (sign(ps[j])? "-" : ""), var(ps[j])+1); 
        }
    printf("0\n");
    }
    // 節の数よりはるかに多く行っている
    // 問題の節の追加以外でも使われている
    // eliminate()でも使われている
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    int nclauses = clauses.size();
    // 途中大きくnclauseが半分ほどになっているところがある(どこ？)
    // test.cnfの場合半分になっているのは1回だけ(50611->24958)
    // 学習節の数は変わらず0

    // use_rcheckはオプション(Check if a clause is already implied)で指定できる(デフォルトでfalse)
    // 何を暗示している？
    // implied:リテラルの配列を受け取ってその中で未定義のリテラル(否定？)をキューに入れてる
    // 何やってるかはよくわからない
    // 普通の実行ではやっていない(オプションでtrueにしないと実行されない？)
    if (use_rcheck && implied(ps))
        return true;

    if (!Solver::addClause_(ps))
        return false;

    // 節の長さが1の時はclausesに追加しないからif以下の実行はしなくていい
    if (use_simplification && clauses.size() == nclauses + 1){
        // 型CRef,Clauseの中身を見たい
        // CRefはどこを参照すればいいかわかるってこと？
        // => ca[CRef]で参照できる？
        // clausesは各要素がCRefのベクトル
        CRef          cr = clauses.last();
        // cはClause型のca[cr]を参照する
        // 参照はポインタの定数版らしいので変更はできない？
        const Clause& c  = ca[cr];

        // NOTE: the clause is added to the queue immediately and then
        // again during 'gatherTouchedClauses()'. If nothing happens
        // in between, it will only be checked once. Otherwise, it may
        // be checked twice unnecessarily. This is an unfortunate
        // consequence of how backward subsumption is used to mimic(真似する)
        // forward subsumption(前向き包含？).
        // Forward subsumption:論理プログラミングや自動定理証明などの分野で使われる用語
        // 一般的に、論理プログラムにおいて1つの節（ルールや事実）が別の節に含まれている場合を指す
        // 具体的には、節 A が節 B に含まれるとき、節 A が節 B を「subsume（包含する）」していると言う
        // そして、もし節 A が節 B を包含し、節 B が節 C を包含しているならば、節 A は節 C を「forward subsume（前向き包含する）」していると言う


        subsumption_queue.insert(cr); // Queue<CRef>型でSimpSolverの中で使われている感じ
        if (false) {
            printf("c= ");
            for (int j = 0; j < c.size(); j++) {
                printf("%s%d ", (sign(c[j])? "-" : ""), var(c[j])+1); 
            }
            printf("0\n");
        }
        // varはリテラルの数字部分を取り出すのでvar(-x),var(x)はどちらもx-1が返ってくる
        for (int i = 0; i < c.size(); i++){
            occurs[var(c[i])].push(cr);
            n_occ[c[i]]++; // n_occはLMap<int>型らしい(そのリテラルが何回出現したか？)
            // printf("touched[var(c[i])]=%d\n", touched[var(c[i])]);
            // touchedの値は0,1のどちらかっぽい
            touched[var(c[i])] = 1; // touchedは何に使う？(確認する必要がある変数ということ？)
            n_touched++;
            // Heap<Var,ElimLt> elim_heap
            // inHeap:heapにあるかどうか
            // Q.increase:何をするやつ？
            //   A.値を大きくする=>heapにおいて下に下げる
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(CRef cr)
{
    const Clause& c = ca[cr];

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[c[i]]--;
            updateElimHeap(var(c[i]));
            occurs.smudge(var(c[i]));
        }
    // fprintf(proof_file, "Simpsolver::removeClause->");
    Solver::removeClause(cr);
}


bool SimpSolver::strengthenClause(CRef cr, Lit l)
{
    if (false) {
        for (int k = 0; k < ca[cr].size(); k++) {
            printf("%s%d ", (sign(ca[cr][k])? "-" : ""), var(ca[cr][k])+1);
        }
        printf("0 -> ");
    }
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);
    assert(use_simplification);

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(cr);

    if (c.size() == 2){
        // fprintf(proof_file, "SimpSolver::strengthenClause->");
        removeClause(cr);
        c.strengthen(l);
    }else{
        detachClause(cr, true);
        c.strengthen(l);
        attachClause(cr);
        remove(occurs[var(l)], cr);
        n_occ[l]--;
        updateElimHeap(var(l));
    }
    //　証明部分
    if (proof_file) {
        for (int k = 0; k < ca[cr].size(); k++) {
            fprintf(proof_file, "%s%d ", (sign(ca[cr][k])? "-" : ""), var(ca[cr][k])+1);
        }
        fprintf(proof_file, "0\n");
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == CRef_Undef : true;
}


// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    merges++;
    out_clause.clear();

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i])){
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
                }
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v)
            out_clause.push(ps[i]);

    return true;
}


// Returns FALSE if clause is always satisfied.
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size)
{
    merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;
    const Lit*  __ps  = (const Lit*)ps;
    const Lit*  __qs  = (const Lit*)qs;

    size = ps.size()-1;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i])){
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
                }
            size++;
        }
        next:;
    }

    return true;
}


// 既にsubsumption_queueにある節にマーク(2)をつける
// ->addClause?の際に一度でも出てきた変数に対して、
//   その変数が含まれる節(マーク(0))をsubsumption_queueに加える
// ->つけたマーク(2)を0に戻す
// Q.単に問題を読むような今回の場合だと追加していない？
//   A.追加していないが２回目、３回目...では追加している
void SimpSolver::gatherTouchedClauses()
{
    // printf("gatherTouchedClauses()を実行します\n");
    // printf("n_touched=%d\n", n_touched);
    // printf(" subsumption_queue.size()=%d\n", subsumption_queue.size());
    if (n_touched == 0) return;

    int i,j;
    // subsumption(包摂)
    // addClauseの中で節をsubsumption_queueに追加をしている
    for (i = j = 0; i < subsumption_queue.size(); i++) {
        // 節の出力はこれであってる
        // ただ節の数は問題の節から減っている(簡約とかで減っている？)
        if (false) {
            printf(" ca[subsumption_queue[i]]= ");
            for (int k = 0; k < ca[subsumption_queue[i]].size(); k++) {
                printf("%s%d ", (sign(ca[subsumption_queue[i]][k])? "-" : ""), var(ca[subsumption_queue[i]][k])+1); 
            }
        printf("0\n");
        }
        // printf(" ca[subsumption_queue[i]].mark()=%d\n", ca[subsumption_queue[i]].mark());
        // Q.markの初期値は？
        //   A.0(->2)(確認したかどうか？)
        if (ca[subsumption_queue[i]].mark() == 0)
            ca[subsumption_queue[i]].mark(2);
        // printf(" ->ca[subsumption_queue[i]].mark()=%d\n", ca[subsumption_queue[i]].mark());
    }

    for (i = 0; i < nVars(); i++)
        if (touched[i]){
            const vec<CRef>& cs = occurs.lookup(i);
            for (j = 0; j < cs.size(); j++)
                if (ca[cs[j]].mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    ca[cs[j]].mark(2);
                }
            touched[i] = 0;
        }

    for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
            ca[subsumption_queue[i]].mark(0);

    // printf(" subsumption_queue.size()=%d\n", subsumption_queue.size());
    n_touched = 0;
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return true;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != CRef_Undef;
    cancelUntil(0);
    return result;
}


// eliminateVarとasymmVarでも使われている
// eliminate()においてはeliminateVarが大量に使われている
// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    // printf("   backwardSubsumptionCheck()を実行します\n");
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
            subsumption_queue.clear();
            bwdsub_assigns = trail.size();
            break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        // 頻繁にif以下は実行されている
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            if (false) {
                printf("    bwdsub_tmpunit=");
                for (int k = 0; k < ca[bwdsub_tmpunit].size(); k++) {
                    printf("%s%d ", (sign(ca[bwdsub_tmpunit][k])? "-" : ""), var(ca[bwdsub_tmpunit][k])+1); 
                }
                printf("0\n");
            }
            subsumption_queue.insert(bwdsub_tmpunit); }

        // キューは先入れ先出し
        // peek()で先頭要素を確認、pop()で先頭要素の削除
        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        // trueは0以外(基本1)、falseは0？
        // Q.なんでtrueを0以外にする？
        //   A.大体の変数は0を初期値にするので何か変更があったら確認したい場合、
        //     条件式に変数を代入することで確認できる
        // test.cnfの場合だと0か1のどっちかしか無かった
        // Q.mark()の数値は2,3には特定の意味がある？
        //   A.0=>初期値
        //     1=>削除済み？
        //     2=>マーク？
        //     3=>何してる？(ぱっと検索した感じ見つからなかった)
        // printf("    c.mark()=%d\n", c.mark());
        // 削除された節に対しては何もしない
        if (c.mark()) {
            // printf("    c.mark()=%d\n", c.mark());
            continue; // continue:後ろの処理を飛ばして次のループへ
        }

        // cntはループ回数(それほど大きな意味はないはず)
        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            printf("subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        // ２つ目の条件式はダミーの節のやつ？
        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        // ここでのbestな変数はその変数を含んでいる節数が一番少ないもの
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        if (false) {
            printf("    c=");
            for (int k = 0; k < c.size(); k++) {
                printf("%s%d ", (sign(c[k])? "-" : ""), var(c[k])+1); 
            }
            printf("0\n");
        }
        // printf("    best=%d, _cs.size()(ループ回数)=%d\n", best+1, _cs.size());
        for (int j = 0; j < _cs.size(); j++){ // _csを使うのはここまで
            if (false) {
            printf("     ca[cs[j]]=");
            for (int k = 0; k < ca[cs[j]].size(); k++) {
                printf("%s%d ", (sign(ca[cs[j]][k])? "-" : ""), var(ca[cs[j]][k])+1); 
            }
            printf("0\n");
            }
            if (c.mark())
                break;
            // subsumption_lim:オプションで指定できる数値
            // 節の大きさがこれ以上の場合はチェックを行わない(-1だと制限無し)
            // 　　　節が削除されていない　かつ　キューから持ってきた節と一緒じゃない　かつ
            // かつ　(subsumption_limが-1(制限無しでチェック)　または　節の大きさがsubsumption_lim未満)
            else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
                // c:キューから持ってきた節(こっちがメイン)
                // best:節cに含まれる変数の中でその変数を含む節の数が一番少なくなるような変数
                // ca[cs[j]]:bestを含む節の一つ(何らかの条件を満たせばこの節を削除する)
                // subsumes(包摂する)
                Lit l = c.subsumes(ca[cs[j]]);

                // 節ca[cs[j]]がcを含んでいる場合
                // (節cに含まれるリテラルが全て節ca[cs[j]]に含まれるリテラルに一致する場合)
                if (l == lit_Undef) {
                    // printf("c.subsumes(ca[cs[j]])=Lit_Undef\n");
                    // removeClauseの中でsolver::removeClauseをやっている
                    // => 前処理をすると証明がおかしくなるのはremoveClauseが原因ではない？
                    // subsumedは消した節の数とイコール(情報出力に使うだけなのでそこまで大きな意味はない)
                    subsumed++, removeClause(cs[j]);
                }
                // 節cに含まれるリテラルorリテラルの否定が全て節ca[cs[j]]に含まれるリテラルに一致する場合
                else if (l != lit_Error){
                    // printf("c.subsumes(ca[cs[j]])=%s%d\n", (sign(l)? "-" : ""), var(l)+1);
                    deleted_literals++;

                    if (false) {
                        for (int k = 0; k < ca[cs[j]].size(); k++) {
                            printf("%s%d ", (sign(ca[cs[j]][k])? "-" : ""), var(ca[cs[j]][k])+1);
                        }
                        printf("0->");
                    }
                    // fprintf(proof_file, "SimpSolver::backwardSubsumptionCheck->");
                    if (!strengthenClause(cs[j], ~l))
                        return false;
                    if (false) {
                        for (int k = 0; k < ca[cs[j]].size(); k++) {
                            printf("%s%d ", (sign(ca[cs[j]][k])? "-" : ""), var(ca[cs[j]][k])+1);
                        }
                        printf("0\n");
                    }

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
                else {
                    // printf("c.subsumes(ca[cs[j]])=lit_Error\n");
                }
            }
        }
    }

    // printf("   backwardSubsumptionCheck()を実行しました\n");
    return true;
}


bool SimpSolver::asymm(Var v, CRef cr)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v && value(c[i]) != l_False)
            uncheckedEnqueue(~c[i]);
        else
            l = c[i];

    if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    // printf("   asymmVar()を実行します\n");
    assert(use_simplification);

    const vec<CRef>& cls = occurs.lookup(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
            return false;

    // printf("   asymmVar()を実行しました\n");
    return backwardSubsumptionCheck();
}


static void mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}



bool SimpSolver::eliminateVar(Var v)
{
    // printf(" eliminateVar()を実行します(v=%d)\n", v+1);
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    const vec<CRef>& cls = occurs.lookup(v);
    vec<CRef>        pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    // Check wether the increase in number of clauses(節の数の増加) stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    int cnt         = 0;
    int clause_size = 0;

    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > cls.size() + grow || (clause_lim != -1 && clause_size > clause_lim))){
                // printf("  if文を実行します\n");
                return true;
            }

    // Delete and store old clauses:
    eliminated[v] = true;
    setDecisionVar(v, false);
    // if (value(v) == l_False) printf("value(v) = l_False\n");
    // else if (value(v) == l_True) printf("value(v) = l_True\n");
    // else if (value(v) == l_Undef) printf("value(v) = l_Undef\n");
    // else printf("value(v) = その他\n");
    // とりあえず削除する変数にはfalseを割り当ててみる
    // => 間違い(削除する変数には何の値も割り振っていない)
    // printf("-%d 0\n", v+1);
    eliminated_vars++;

    if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
            mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
    }else{
        for (int i = 0; i < pos.size(); i++)
            mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
    }

    for (int i = 0; i < cls.size(); i++)
        removeClause(cls[i]); 

    // Produce clauses in cross product:
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
                return false;

    // Free occurs list for this variable:
    occurs[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    if (watches[ mkLit(v)].size() == 0) watches[ mkLit(v)].clear(true);
    if (watches[~mkLit(v)].size() == 0) watches[~mkLit(v)].clear(true);

    // printf("   eliminateVar()を実行しました\n");
    return backwardSubsumptionCheck();
}


bool SimpSolver::substitute(Var v, Lit x)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    if (!ok) return false;

    eliminated[v] = true;
    setDecisionVar(v, false);
    const vec<CRef>& cls = occurs.lookup(v);
    
    vec<Lit>& subst_clause = add_tmp;
    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];

        subst_clause.clear();
        for (int j = 0; j < c.size(); j++){
            Lit p = c[j];
            subst_clause.push(var(p) == v ? x ^ sign(p) : p);
        }

        removeClause(cls[i]);

        if (!addClause_(subst_clause))
            return ok = false;
    }

    return true;
}


void SimpSolver::extendModel()
{
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
            if (modelValue(toLit(elimclauses[i])) != l_False)
                goto next;

        x = toLit(elimclauses[i]);
        model[var(x)] = lbool(!sign(x));
    next:;
    }
}


// turn_off_elim:eliminate()を実行した後に必要なデータを消すか
// (その後にeliminate()をしようとしても何もしない)
bool SimpSolver::eliminate(bool turn_off_elim)
{
    // printf("実行開始:SimpSolver::eliminate()\n");
    // printf("nassigns=%d\n", nAssigns());
    // simplify()でfalseが返ってくるのはsimplify()の中のプロパゲーションで矛盾が起きる場合かソルバーをこれ以上動かしてはいけない場合
    if (!simplify()) // -> core/solver.cc
        return false;
    else if (!use_simplification){
        // 一度eliminate()を行うとuse_simplification=falseになってここを通る(後で変わる可能性もなくはない)
        return true;
    }
    // printf("nassigns=%d\n", nAssigns());

    // Main simplification loop:
    //
    // -no-preにするとwhileの中に入らない
    // test.cnfの場合途中抜けしないで８回ループしてる？
    // printf(" bwdsub_assigns=%d\n", bwdsub_assigns);
    // bwdsub_assignsの初期値は0
    // bwd=backward?
    while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){
        // printf(" ループ上部\n");

        // printf("n_touched=%d(>0?) || bwdsub_assigns=%d (<?) trail.size()=%d || elim_heap.size()=%d (>0?)\n", n_touched, bwdsub_assigns, trail.size(), elim_heap.size());
        // Q.gatherTouchedClauses()を消すとどうなる？
        //   A.原因はわからないがwhile内を抜けられなくなる
        gatherTouchedClauses(); // -> simp/SimpSolver.cc
        // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
        // printf("  (1)bwdsub_assigns=%d, trail.size()=%d\n", bwdsub_assigns, trail.size());
        // backwardSubsumptionCheckを行うとbwdsub_assigns, trail.size()の値が変わる
;        if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) && 
            !backwardSubsumptionCheck(true)){
            ok = false; goto cleanup; }
        // printf("  (2)bwdsub_assigns=%d, trail.size()=%d\n", bwdsub_assigns, trail.size());
        // Empty elim_heap and return immediately on user-interrupt:
        if (asynch_interrupt){
            assert(bwdsub_assigns == trail.size());
            assert(subsumption_queue.size() == 0);
            assert(n_touched == 0);
            elim_heap.clear();
            goto cleanup; }

        // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
        // printf("  forループ開始, elim_heap.size()=%d\n", elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            // printf("   ループ%d回目, elim_heap.size()=%d\n", cnt+1, elim_heap.size());
            Var elim = elim_heap.removeMin();
            // printf("    elim=%d\n", elim+1);
            
            if (asynch_interrupt) break;

            if (isEliminated(elim) || value(elim) != l_Undef) {
                // printf("    isEliminated(elim) || value(elim) != l_Undef=trueです\n");
                continue;
            }

            if (verbosity >= 2 && cnt % 100 == 0)
                printf("elimination left: %10d\r", elim_heap.size());

            // use_asymm:オプション(デフォルトはfalse)
            // デフォルトはfalseだからここのif文は実行されない
            if (use_asymm){
                // printf("    use_asym=trueです\n");
                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                bool was_frozen = frozen[elim];
                frozen[elim] = true;
                if (!asymmVar(elim)){
                    ok = false; goto cleanup; }
                frozen[elim] = was_frozen; }

            // At this point, the variable may have been set by assymetric branching, so check it
            // again. Also, don't eliminate frozen variables:
            // printf("    frozen[elim]=%s\n", frozen[elim]? "true" : "false");
            // use_asymmがfalseだからかfrozen[elim]は全てfalse
            if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                ok = false; goto cleanup; }

            checkGarbage(simp_garbage_frac);
        }

        assert(subsumption_queue.size() == 0);
        // printf(" bwdsub_assigns=%d\n", bwdsub_assigns);
        // printf(" ループ下部\n");
    }
 cleanup: // gotoのラベル

    // If no more simplification is needed, free all simplification-related data structures:
    if (turn_off_elim){
        touched  .clear(true);
        occurs   .clear(true);
        n_occ    .clear(true);
        elim_heap.clear(true);
        subsumption_queue.clear(true);

        use_simplification    = false;
        remove_satisfied      = true;
        ca.extra_clause_field = false;
        max_simp_var          = nVars();

        // Force full cleanup (this is safe and desirable since it only happens once):
        rebuildOrderHeap();
        garbageCollect();
    }else{
        // Cheaper cleanup:
        checkGarbage();
    }

    if (verbosity >= 1 && elimclauses.size() > 0)
        printf("|  Eliminated clauses:     %10.2f Mb                                      |\n", 
               double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024));

    // printf("実行終了:SimpSolver::eliminate()\n");
    return ok;
}


//=================================================================================================
// Garbage Collection methods:


void SimpSolver::relocAll(ClauseAllocator& to)
{
    if (!use_simplification) return;

    // All occurs lists:
    //
    for (int i = 0; i < nVars(); i++){
        occurs.clean(i);
        vec<CRef>& cs = occurs[i];
        for (int j = 0; j < cs.size(); j++)
            ca.reloc(cs[j], to);
    }

    // Subsumption queue:
    //
    for (int i = subsumption_queue.size(); i > 0; i--){
        // CRef crは節の場所を表す(ca[cr]で参照できる)
        CRef cr = subsumption_queue.peek(); subsumption_queue.pop();
        if (ca[cr].mark()) continue;
        ca.reloc(cr, to);
        subsumption_queue.insert(cr);
    }
        
    // Temporary clause:
    //
    ca.reloc(bwdsub_tmpunit, to);
}


void SimpSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.
    relocAll(to);
    Solver::relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
