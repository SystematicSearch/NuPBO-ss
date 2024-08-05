#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>
#include <stdio.h>
#include <stdlib.h>
#include <sys/times.h>
#include <unistd.h>
#include <signal.h>
#include <algorithm>
#include <map>
#include "string_util.h"

using namespace std;

#define mypop(stack) stack[--stack##_fill_pointer]
#define mypush(item, stack) stack[stack##_fill_pointer++] = item

/* ----------------------------------------------- added parameters ----------------------------------------------- */

constexpr bool use_presolve                   = false;
constexpr bool use_runtime_unit_propagate     = true;
constexpr bool use_propagate_size_limit       = true;
constexpr int  propagate_size_limit           = 10;
constexpr int  num_cand_in_propagate          = 5;
constexpr int  init_local_optima_thres        = 10;
constexpr int  local_optima_thres_multiplier  = 256;
constexpr bool use_final_attempt              = false;
constexpr int  final_attempt_looptime         = 15;
constexpr double double_tol = 1e-6;
/* -------------------------------------------- end of added parameters -------------------------------------------- */

/* --------------------------------------------- added data structure --------------------------------------------- */
struct var_with_sense
{
    var_with_sense() = default;
    var_with_sense(int u, int b)
    {
        id = u;
        sense = b;
    };
    int id   {0};
    int sense{0};
};

/* Implication table */
enum class imply_level { empty, clique, clause, formula };
class ImplicationTable
{
public:
    double time{0};
    size_t var_num{0};
    map<uint32_t, vector<uint32_t>> clique_index;
    vector<vector<var_with_sense>> table;
    vector<imply_level> flag;
    ImplicationTable() = default;
    explicit ImplicationTable(size_t v);
    void AddClique(int c);
    void Init();

    vector<var_with_sense>& GetFormulaLevel(int v, int sense);
    vector<var_with_sense>& GetClauseLevel(int v, int sense);
    vector<var_with_sense>& GetCliqueLevel(int v, int sense);
    vector<var_with_sense>& GetTable(int v, int sense);
    vector<var_with_sense>& GetCurrTable(int v, int sense);
};

// propagate
extern int               local_optima_thres;
extern int               local_optima_count;
extern long long         num_propagate_called;
extern long long         num_backtrack;
extern double            propagate_success_len;
extern double            propagate_fail_len;
extern ImplicationTable imply_table;

// extended propagate strategy
extern int               final_attempt_attempt;
extern int               final_attempt_success;
extern int               final_attempt_state;

// presolve
extern int*              fixed_sense;
extern bool              proved_unsat;
extern long long         soft_fixed_cost;

// other statistics
extern vector<long long> opt_soln_update_history;
extern vector<double>    opt_soln_update_time;
extern long long         total_step;

inline int to_index(int v, int sense) { return (v << 1) + sense; }

class FlipRecord{
public:
    FlipRecord() = default;
    explicit FlipRecord(int x) {
        capacity = x;
        index = new int[capacity];
        memset(index, -1, capacity * sizeof(int));
        queue = new int[capacity];
    }
    ~FlipRecord() {
        delete[] index;
        delete[] queue;
    }
    int capacity{0};
    int* index{};
    int* queue{};
    int size{0};
    int first_flip_var{0};
    bool first_flip_var_sense_before{false};

    inline void SetFirstFlip(int v, bool s) {
        first_flip_var = v;
        first_flip_var_sense_before = s;
    }

    inline int tail() {
        if (size > 0) {
            return queue[size - 1];
        } else
            exit(-1);
    }

    inline void remove_tail() {
        int tail = queue[--size];
        index[tail] = -1;
    }

    inline void remove(int v) {
        int idx = index[v];
        int tail = queue[--size];
        queue[idx] = tail;
        index[tail] = idx;
        index[v] = -1;
    }

    inline void push(int v) {
        if (index[v] != -1) {
            remove(v);
            return;
        }
        index[v] = size;
        queue[size++] = v;
    }
    inline void clear() {
        for (int i = 0; i < size; ++i) {
            index[queue[i]] = -1;
        }
        size = 0;
    }
};

extern FlipRecord* propagate_record;
extern long long count_local_opt_method_bt;

template <typename ItemType, typename ScoreType, typename TimeStampType> class CandFilter
{
public:
    vector<ScoreType> scoreVec;
    vector<TimeStampType> timeStampVec;
    vector<ItemType> itemVec;
    bool full{false};
    uint32_t size{10};
    explicit CandFilter(uint32_t s) {
        size = s;
        scoreVec.reserve(size);
        timeStampVec.reserve(size);
        itemVec.reserve(size);
    }
    CandFilter() = default;
    void Insert(ItemType& item, ScoreType score, TimeStampType timeStamp) {
        for (auto& currItem: itemVec) {
            if (item == currItem) { return; }
        }

        if (!full) {
            itemVec.push_back(item);
            scoreVec.push_back(score);
            timeStampVec.push_back(timeStamp);
            if (itemVec.size() == size) { full = true; }
            return;
        }
        ItemType tmpItem = item;
        ScoreType tmpScore = score;
        TimeStampType tmpTimeStamp = timeStamp;
        for (size_t i = 0; i < size; ++i) {
            if (scoreVec[i] > tmpScore + double_tol) { continue; }
            if (scoreVec[i] > tmpScore - double_tol && tmpScore > scoreVec[i] - double_tol) {
                if (timeStampVec[i] < tmpTimeStamp) { continue; }
                if (timeStampVec[i] == tmpTimeStamp && rand() % 2 == 1) { continue; }
            }
            tmpItem = itemVec[i];
            itemVec[i] = tmpItem;
            tmpScore = scoreVec[i];
            scoreVec[i] = tmpScore;
            tmpTimeStamp = timeStampVec[i];
            timeStampVec[i] = tmpTimeStamp;
        }
    }
    bool IsEmpty() {
        return itemVec.empty();
    }
};


/* ------------------------------------------- end of  added data structure ------------------------------------------- */

/* const */
const float MY_RAND_MAX_FLOAT = 10000000.0;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001; // 1.0f/MY_RAND_MAX_FLOAT;


/* Data structure for a literal */
struct lit
{
    int clause_num; // clause num, begin with 0
    int var_num;	// variable num, begin with 1
    int weight;
    bool sense;		// 1 for true literals, 0 for false literals.
};


struct var_with_weight
{
    int var_num;
    int weight;
};
extern var_with_weight* temp_unsat;

/* basic info */
extern int*   temp_array;
extern struct tms start_time;
extern double hard_clause_weight_sum;
extern double soft_clause_weight_increased;

extern int*   new_unsat_hard_clause_stack;
extern int    new_unsat_hard_clause_stack_fill_pointer;
extern double avg_neighbor_lit;


/* Information about the clauses */
extern long long top_clause_weight;
extern long long *org_clause_weight;
extern double *tune_soft_clause_weight;
extern double *unit_weight;
extern double *tuned_degree_unit_weight;

extern int *sat_count;
extern int *sat_var;
extern int* soft_clause_num_index;
extern int* hard_clause_num_index;

extern string path;

// size of the instance
extern int num_vars;	// var index from 1 to num_vars
extern int num_clauses; // clause index from 0 to num_clauses-1
extern int num_hclauses;
extern int num_sclauses;

// steps and time
extern int tries;
extern int max_tries;
extern unsigned int max_flips;
extern unsigned int max_non_improve_flip;
extern unsigned int step;

extern double opt_time;

/* literal arrays */
extern lit **var_lit;		  // var_lit[i][j] means the j'th literal of variable i.
extern int *var_lit_count;	  // amount of literals of each variable
extern lit **clause_lit;	  // clause_lit[i][j] means the j'th literal of clause i.
extern int *clause_lit_count; // amount of literals in each clause
extern int *clause_true_lit_thres;
extern int *clause_coef_sum;
extern double *avg_clause_coe;

/* Information about the variables. */
extern double *hscore;
extern double *sscore;
extern long long *time_stamp;
extern int **var_neighbor;
extern int *var_neighbor_count;
extern int *neighbor_flag;
extern int *temp_neighbor;

// unsat clauses stack
extern int *hardunsat_stack;		  // store the falsified clause number
extern int *index_in_hardunsat_stack; // which position is a clause in the unsat_stack
extern int hardunsat_stack_fill_pointer;

extern int *softunsat_stack;		  // store the falsified clause number
extern int *index_in_softunsat_stack; // which position is a clause in the unsat_stack
extern int softunsat_stack_fill_pointer;

// good decreasing variables (dscore>0)
extern int *goodvar_stack;
extern int goodvar_stack_fill_pointer;
extern int *already_in_goodvar_stack;

/* Information about solution */
extern int *cur_soln; // the current assignment, with 1's for True variables, and 0's for False variables
extern int *best_soln;
extern int best_soln_feasible; // when find a feasible solution, this is marked as 1.
extern int local_soln_feasible;
extern int hard_unsat_nb;
extern long long soft_unsat_weight;
extern long long opt_unsat_weight;
extern long long local_opt_unsat_weight;
extern long long best_known;

// parameters used in algorithm
extern float rwprob;
extern float rdprob;
extern int hd_count_threshold;
extern int h_inc;
extern int s_inc;
extern float initsoftw;


void parse_instance_scale(ifstream& infile);
void build_instance(const char *filename);
void count_soft_clauses(ifstream& infile);
void check_operations(ifstream& infile);
void parse_soft_clauses(ifstream& infile, int& c);
void parse_hard_clauses(ifstream& infile, int& c);
bool build_ge_constarint(int& c, string& left, int right);
bool build_ge_constarint_impl(int& c, vector<int>& indices, vector<int>& coefs, int degree);
void build_eq_constraint(int& c, string& left, int right);
void parse_left(string& left, vector<int>& coefs, vector<int>& indices, int& neg_count);
bool check_soln_in_org_instance(const char *filename);
void local_search(vector<int> &init_solution, const char *inputfile);
void update_best_soln();
void simple_print();
void print_best_solution();
void free_memory();
void check_new_score();
void check_softunsat_weight();
void start_timing();
double get_runtime();


// function used in algorithm
void build_neighbor_relation();
void build_var_lit(bool malloc);
void allocate_memory();
bool verify_sol();
void increase_weights();
void update_clause_weights();
void unsat(int clause);
void sat(int clause);
void init_local_search(vector<int> &init_solution);
void flip(int flipvar);
void update_goodvarstack(int flipvar);
int pick_var();
void settings();
void handle_local_optima();
void print_features();


enum class DfsVisitSense { Visited, NotVisited, VisitedAndEnd };
enum class PropagateSense { POS, NEG, NOTHING };

class Presolve
{
public:
    void Run();
    void Init();
    explicit Presolve() { Init(); }
    vector<int>         checkList_;
    vector<int>         indexInCheckList_;
    size_t              checkListFillPointer_{0};

    void CheckConstraint(int c);
    void FixVarByTerm(lit& t);
    void FixVarBySense(int v, bool sense);
    void ClearZeroCoefTerms();
    void ClearZeroCoefTermInConstr(int c, int eraseCount);

    void Saturate  (int c);
    void Divide    (int c);
    void ToCardinal(int c);
    void ToPlanted (int c);

};

inline bool IsFixed(int v) {
    return fixed_sense[v] >= 0;
}

inline int gcd(int a, int b) {
    if (b) while ((a %= b) && (b %= a));
    return a + b;
}


/* useful inline functions */
inline double GetHClausePunish(int c) {
    return tuned_degree_unit_weight[c] * (clause_true_lit_thres[c] - sat_count[c]);
}

inline double GetSClausePunish(int c) {
    return unit_weight[c] * tune_soft_clause_weight[c] * (clause_true_lit_thres[c] - sat_count[c]);
}

void print_opb();
#endif
