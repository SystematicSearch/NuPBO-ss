#include "basis_pms.h"
#include "init.h"
#include "heuristic.h"

#include <stdio.h>
#include <string>
#include <iostream>
#include <cmath>
#include <sstream>
#include <algorithm>
#include <regex>

/* not checked */
int final_attempt_state = 0;
int final_attempt_attempt = 0;
int final_attempt_success = 0;

/* added things */
string path;
double propagate_success_len = 0;
double propagate_fail_len = 0;

double hard_clause_weight_sum = 0;
double soft_clause_weight_increased = 0;
int* new_unsat_hard_clause_stack;
int new_unsat_hard_clause_stack_fill_pointer;
int* fixed_sense;
long long count_local_opt_method_bt = 0;

FlipRecord* propagate_record;
vector<long long> opt_soln_update_history;
vector<double> opt_soln_update_time;

ImplicationTable imply_table;

map<int, bool> fixedSense;
bool proved_unsat = false;
double avg_neighbor_lit = 0;
double total_propagate_len = 0;
long long num_propagate_called = 0;
long long num_backtrack = 0;
map<int, bool> flip_var_record;

int *temp_array = NULL;
var_with_weight *temp_unsat = NULL;
int *soft_clause_num_index = NULL;
int *hard_clause_num_index = NULL;
long long total_step;
int is_print;
long long soft_fixed_cost = 0;
double read_finish_time = 0;
int local_optima_count = 0;
int local_optima_thres = init_local_optima_thres;

// size of the instance
int num_vars = 0;	  // number of variables, var index from 1 to num_vars
int num_clauses = 0;  // number of clauses, clause index from 0 to num_clauses-1
int num_hclauses = 0; // number of hard clauses
int num_sclauses = 0; // number of soft clauses

// steps and time
int tries;
int max_tries;
unsigned int max_flips;
unsigned int step_for_propagate;
unsigned int max_non_improve_flip;
unsigned int step;

int cutoff_time = 300;
double opt_time;

/* literal arrays */
lit **var_lit;		   // var_lit[i][j] means the j'th literal of variable i
int *var_lit_count;	   // amount of literals of each variable
lit **clause_lit;	   // clause_lit[i][j] means the j'th literal of clause i.
int *clause_lit_count; // amount of literals in each clause
int *clause_true_lit_thres;
int *clause_coef_sum;
double *avg_clause_coe;

/* Information about the variables. */
double *hscore;
double *sscore;
long long *time_stamp;
int **var_neighbor;
int *var_neighbor_count;
int *neighbor_flag;
int *temp_neighbor;

/* Information about the clauses */
long long top_clause_weight;
long long *org_clause_weight;
double *tune_soft_clause_weight;  // org_clause_weight/avg_soft_weight
double *unit_weight;              // += s_inc; each update
double *tuned_degree_unit_weight = NULL;

int *sat_count;
int *sat_var;

// unsat clauses stack
int *hardunsat_stack;		   // store the falsified clause number
int *index_in_hardunsat_stack; // which position is a clause in the hardunsat_stack
int hardunsat_stack_fill_pointer;

int *softunsat_stack;		   // store the falsified clause number
int *index_in_softunsat_stack; // which position is a clause in the softunsat_stack
int softunsat_stack_fill_pointer;

// good decreasing variables (dscore>0)
int *goodvar_stack;
int goodvar_stack_fill_pointer;
int *already_in_goodvar_stack;

/* Information about solution */
int *cur_soln; // the current assignment, with 1's for True variables, and 0's for False variables
int *best_soln;
int best_soln_feasible; // when find a feasible solution, this is marked as 1.
int local_soln_feasible;
int hard_unsat_nb;
long long soft_unsat_weight;
long long opt_unsat_weight;
long long local_opt_unsat_weight;
long long best_known;

// parameters used in algorithm
float rwprob;
float rdprob;
int hd_count_threshold;
int h_inc;
int s_inc;
float initsoftw = 0;

struct tms start_time;

bool compare(var_with_weight a, var_with_weight b)
{
	return abs(a.weight) > abs(b.weight);
}

void settings()
{
	// steps
	total_step = 0;
	max_tries = 100000000;
	max_flips = 10000000;
	max_non_improve_flip = 10000000;

	rdprob = 0.01;
	rwprob = 0.1;
	hd_count_threshold = 15;
	h_inc = 1;
	s_inc = 1;

	best_known = -2;
	if (num_vars > 2000)
	{
		rdprob = 0.01;
		rwprob = 0.1;
		hd_count_threshold = 50;
	}
	hard_var_greedy_ptr = var_greedy_score;
	soft_var_greedy_ptr = var_greedy_score;
}

void allocate_memory()
{
	int malloc_var_length = num_vars + 10;
	int malloc_clause_length = num_clauses + 10;

    new_unsat_hard_clause_stack = new int[malloc_clause_length];

    fixed_sense = new int[malloc_var_length];
    memset(fixed_sense, -1, malloc_var_length * sizeof(int));

	temp_unsat = new var_with_weight[malloc_var_length];
	temp_array = new int[malloc_clause_length];


	var_lit = new lit *[malloc_var_length];
	var_lit_count = new int[malloc_var_length]();
	clause_lit = new lit *[malloc_clause_length];
	clause_lit_count = new int[malloc_clause_length]();
	clause_true_lit_thres = new int[malloc_clause_length];
    clause_coef_sum = new int[malloc_clause_length];
	avg_clause_coe = new double[malloc_clause_length]();

	hscore = new double[malloc_var_length];
	sscore = new double[malloc_var_length];
	var_neighbor = new int *[malloc_var_length];
	var_neighbor_count = new int[malloc_var_length];
	time_stamp = new long long[malloc_var_length];
	neighbor_flag = new int[malloc_var_length];
	temp_neighbor = new int[malloc_var_length];

	soft_clause_num_index = new int[malloc_clause_length];
	hard_clause_num_index = new int[malloc_clause_length];
	org_clause_weight = new long long[malloc_clause_length];
	tune_soft_clause_weight = new double[malloc_clause_length];
	unit_weight = new double[malloc_clause_length];
	tuned_degree_unit_weight = new double[malloc_clause_length];
	sat_count = new int[malloc_clause_length];
	sat_var = new int[malloc_clause_length];

	hardunsat_stack = new int[malloc_clause_length];
	index_in_hardunsat_stack = new int[malloc_clause_length];
	softunsat_stack = new int[malloc_clause_length];
	index_in_softunsat_stack = new int[malloc_clause_length];

	goodvar_stack = new int[malloc_var_length];
	already_in_goodvar_stack = new int[malloc_var_length];

	cur_soln = new int[malloc_var_length];
	best_soln = new int[malloc_var_length];

    imply_table = ImplicationTable(num_vars);

    propagate_record = new FlipRecord(malloc_var_length);
}

void free_memory()
{
	int i;
	for (i = 0; i < num_clauses; i++)
		delete[] clause_lit[i];

	for (i = 1; i <= num_vars; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
    delete[] new_unsat_hard_clause_stack;

    delete[] fixed_sense;
	delete[] temp_array;
	delete[] temp_unsat;
	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] clause_true_lit_thres;
	delete[] clause_coef_sum;
	delete[] avg_clause_coe;

	delete[] hscore;
	delete[] sscore;
	delete[] var_neighbor;
	delete[] var_neighbor_count;
	delete[] time_stamp;
	delete[] neighbor_flag;
	delete[] temp_neighbor;

	delete[] soft_clause_num_index;
	delete[] hard_clause_num_index;
	delete[] org_clause_weight;
	delete[] tune_soft_clause_weight;
	delete[] unit_weight;
	delete[] tuned_degree_unit_weight;
	delete[] sat_count;
	delete[] sat_var;

	delete[] hardunsat_stack;
	delete[] index_in_hardunsat_stack;
	delete[] softunsat_stack;
	delete[] index_in_softunsat_stack;

	delete[] goodvar_stack;
	delete[] already_in_goodvar_stack;

	delete[] cur_soln;
	delete[] best_soln;
    delete propagate_record;
}

regex SCALE_REGEX(R"(#variable=\s*(\d+)\s*#constraint=\s*(\d+))");
regex TERM_REGEX(R"(([-+]?\s*\d*\.?\d+)\s*(x\d+))");
regex EQUALITY_REGEX(R"((<=|>=|==|=|<|>))");
regex END_REGEX(R"(\s*([-+]?\d+)\s*;)");

void build_neighbor_relation()
{
	//cout << "c start build neighbor" << endl;
	int i, j, count;
	int v, c, n;
	int temp_neighbor_count;

	for (v = 1; v <= num_vars; ++v)
	{
		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;

		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for (j = 0; j < clause_lit_count[c]; ++j)
			{
				n = clause_lit[c][j].var_num;
				if (neighbor_flag[n] != 1)
				{
					neighbor_flag[n] = 1;
					temp_neighbor[temp_neighbor_count++] = n;
				}
			}
		}

		neighbor_flag[v] = 0;
		var_neighbor[v] = new int[temp_neighbor_count];
		var_neighbor_count[v] = temp_neighbor_count;

		count = 0;
		for (i = 0; i < temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}
	}
}

void parse_left(string& left, vector<int>& coefs, vector<int>& indices, int& neg_count)
{
    neg_count = 0;
    smatch match;
    string::const_iterator search_start(left.cbegin());

    while (regex_search(search_start, left.cend(), match, TERM_REGEX)) {
        string coef_str = match[1];
        string index_str = match[2];
        coef_str.erase(remove_if(coef_str.begin(), coef_str.end(), ::isspace), coef_str.end());
        coefs.push_back(stoi(coef_str));
        indices.push_back(stoi(index_str.substr(1)));
        double coef_tmp = stod(coef_str);
        if (coef_tmp - floor(coef_tmp) > 1e-6) {
            cout << "coef not int: " << coef_tmp << endl;
            exit(-1);
        } else if (coef_tmp > INT32_MAX || coef_tmp < INT32_MIN) {
            cout << "coef out of range: " << coef_tmp << endl;
            exit(-1);
        }
        int coef = stoi(coef_str);
        if (coef < 0) {
            neg_count -= coef;
        }
        search_start = match.suffix().first;
    }

}

bool build_ge_constarint(int& c, string& left, int right)
{
    int neg_count = 0;
    vector<int> indices;
    vector<int> coefs;

    parse_left(left, coefs, indices, neg_count);
    build_ge_constarint_impl(c, indices, coefs, neg_count + right);
}

bool build_ge_constarint_impl(int& c, vector<int>& indices, vector<int>& coefs, int degree)
{
    int skip = 0;
    clause_true_lit_thres[c] = degree;
    clause_lit_count[c] = coefs.size();

    // always satisfied clause will not generate
    if (clause_true_lit_thres[c] <= 0) { return false; }

    if (use_presolve) {
        // check fix status
        for (int i = 0; i < clause_lit_count[c]; ++i) {
            int v = indices[i];
            int w = coefs[i];
            if (IsFixed(v)) {
                skip++;
                if (fixed_sense[v] == static_cast<int>(w > 0)) {
                    clause_true_lit_thres[c] -= abs(w);
                }
            }
        }
        if (clause_true_lit_thres[c] <= 0 || skip == clause_lit_count[c]) {
            return false;
        }
    }
    // create new clause
    clause_lit[c] = new lit[clause_lit_count[c] - skip + 1];

    bool is_cardinal = false; // check cardinality
    int i = 0;
    int j = 0;
    int sum_coeff = 0;
    int d = 1;

    if (use_presolve) {
        int64_t smallSum = 0;     // check planting
        int64_t largeSum = 0;
        if (abs(coefs[0]) > 1) {
            // To cardinal
            int tmp_skip_i = 0;
            int tmp_skip_j = 0;
            while (smallSum < clause_true_lit_thres[c] && i < clause_lit_count[c]) {
                auto pos = clause_lit_count[c] - i - 1;
                i++;
                if (IsFixed(indices[pos])) {
                    tmp_skip_i++;
                    continue;
                }
                smallSum += abs(coefs[pos]);
            }
            while (largeSum < clause_true_lit_thres[c] && j < clause_lit_count[c]) {
                auto pos = clause_lit_count[c] - i - 1;
                j++;
                if (IsFixed(indices[pos])) {
                    tmp_skip_j++;
                    continue;
                }
                largeSum += abs(coefs[pos]);
            }
            i -= tmp_skip_i;
            j -= tmp_skip_j;
            if (i == j) {
                is_cardinal = true;
            } else {
                // saturate and divide
                i = 0;
                d = clause_true_lit_thres[c];
                while ((abs(coefs[i]) >= clause_true_lit_thres[c] || IsFixed(indices[i]))
                       && i < clause_lit_count[c]) { ++i; }
                for (; i < clause_lit_count[c]; ++i) {
                    if (IsFixed(indices[i])) { continue; }
                    d = gcd(d, abs(coefs[i]));
                    if (d <= 1) break;
                }
            }
        }
    }
    int fill_pointer = 0;
    if (is_cardinal) {
        for (i = 0; i < clause_lit_count[c]; ++i) {
            if (IsFixed(indices[i])) { continue; }
            auto& term = clause_lit[c][fill_pointer++];
            term.clause_num = c;
            term.var_num = indices[i];
            term.weight = 1;
            term.sense = (coefs[i] > 0);
        }
        clause_lit_count[c] = fill_pointer;
        clause_true_lit_thres[c] = j;
        sum_coeff = fill_pointer;
    } else {

        for (i = 0; i < clause_lit_count[c]; ++i) {
            if (IsFixed(indices[i])) { continue; }
            int tmp_coef = min(abs(coefs[i]), clause_true_lit_thres[c]) / d;
            if (tmp_coef == 0) {
                skip++;
                continue;
            }
            auto &term = clause_lit[c][fill_pointer++];

            term.clause_num = c;
            term.var_num = indices[i];
            term.weight = tmp_coef;
            term.sense = (coefs[i] > 0);
            sum_coeff += term.weight;
            if (term.weight < 0) {
                cout << "?" << endl;
            }
        }
        if (d > 1) {
            auto &degree = clause_true_lit_thres[c];
            if (degree % d == 0) {
                degree /= d;
            } else {
                degree /= d;
                degree++;
            }
        }
    }

    // end of clause
    clause_lit_count[c] = fill_pointer;
    if (clause_lit_count[c] == 0) {
        delete[] clause_lit[c];
        return false;
    }

    clause_lit[c][clause_lit_count[c]].var_num = 0;
    clause_lit[c][clause_lit_count[c]].clause_num = -1;
    clause_lit[c][clause_lit_count[c]].weight = 0;
    clause_coef_sum[c] = sum_coeff;
    avg_clause_coe[c] = round(double(clause_coef_sum[c] / (double)clause_lit_count[c]));
    org_clause_weight[c] = top_clause_weight;
    hard_clause_num_index[num_hclauses++] = c;

    for (i = 0; i < clause_lit_count[c]; ++i) {
        var_lit_count[clause_lit[c][i].var_num]++;
    }
    ++c;
    return true;
}

void build_eq_constraint(int& c, string& left, int right)
{
    int neg_count = 0;
    clause_true_lit_thres[c] = right;
    vector<int> indices;
    vector<int> coefs;

    parse_left(left, coefs, indices, neg_count);

    int i;
    int odd_num = 0;
    int odd_index_1 = -1;
    int oddity_of_thres = abs(clause_true_lit_thres[c] % 2);

    if (use_presolve) {
        for (i = 0; i < clause_lit_count[c]; ++i) {
            int v = indices[i];
            if (IsFixed(v) && (coefs[i] > 0) == fixed_sense[v]) {
                oddity_of_thres += abs(coefs[i] % 2);
                continue;
            }
            if (abs(coefs[i] % 2) == 1) {
                // CAUTION: -1 % 2 == -1
                odd_num++;
                if (odd_num == 1) {
                    odd_index_1 = i;
                } else {
                    break;
                }
            }
        }

        if (odd_num == 1) {
            // fix the odd term
            //    3x1 + ... = 2:  sense>0 thres%2=0  x1 = 0
            //    3x1 + ... = 3:  sense>0 thres%2=1  x1 = 1
            //    -3x1 + ... = 3: sense<0 thres%2=1  x1 = 0
            //    -3x1 + ... = 2: sense<0 thres%2=0  x1 = 1
            int fixed_var_num = indices[odd_index_1];
            fixed_sense[fixed_var_num] = static_cast<int>((oddity_of_thres % 2) ==
                                                          static_cast<int>(coefs[odd_index_1] > 0));
        }
    }
    int tmp_sum_coef = 0;
    for (i = 0; i < coefs.size(); ++i) {
        tmp_sum_coef += abs(coefs[i]);
    }
    // get ready for next clause
    auto count_cpy = coefs.size();
    auto thres_cpy = tmp_sum_coef - clause_true_lit_thres[c] - neg_count;

    if (!build_ge_constarint_impl(c, indices, coefs, right + neg_count)) {
        num_clauses--;
    }

    // make copy
    clause_lit_count[c] = count_cpy;
    clause_true_lit_thres[c] = thres_cpy;
    for (i = 0; i < clause_lit_count[c]; ++i)
    {
        coefs[i] = -coefs[i];
    }

    if (!build_ge_constarint_impl(c, indices, coefs, thres_cpy)) {
        num_clauses--;
    }

}

void parse_instance_scale(ifstream& infile) {
    string line;
    getline(infile, line);
    smatch match;
    string::const_iterator search_start(line.cbegin());
    if (regex_search(search_start, line.cend(), match, SCALE_REGEX)) {
        num_vars = stoi(match[1]) + 1;
        num_clauses = stoi(match[2]) + 1;
#ifdef DEBUG
        cout << "read num_vars = " << num_vars << endl;
        cout << "read num_hclauses = " << num_hclauses << endl;
#endif
    }
}

void count_soft_clauses(ifstream& infile)
{
    string line;
    string coef_str;
    string index_str;

    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        smatch match;
        string::const_iterator search_start(line.begin());
        while (regex_search(search_start, line.cend(), match, TERM_REGEX)) {
            coef_str = match[1];
            index_str = match[2];
            coef_str.erase(remove_if(coef_str.begin(), coef_str.end(), ::isspace), coef_str.end());
            index_str.erase(remove_if(index_str.begin(), index_str.end(), ::isspace), index_str.end());

            auto coef = stoll(coef_str);
            if (coef > INT32_MAX || coef < INT32_MIN) {
                cout << "Term coef out of range: int32_t." << endl;
                exit(-1);
            }

            auto index = stoi(index_str.substr(1));
            if (index > 1e10) {
                cout << "Index out of range: 1e10." << endl;
                exit(-1);
            }
            if (index > num_vars) {
                num_vars = index;
            }
            num_sclauses++;
            search_start = match.suffix().first;
        }

        if (line.find(';') != string::npos) {
            break;
        }
    }
#ifdef DEBUG
    cout << "read num_sclauses = " << num_sclauses << endl;
#endif
}

void check_operations(ifstream& infile)
{
    string line;
    string constraint;

    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        constraint += line + " ";

        /* read until ; */
        if (line.find(';') == string::npos) { continue; }

        /* split */
        smatch formulaMatch;
        if (regex_search(constraint, formulaMatch, EQUALITY_REGEX)) {
            string op = formulaMatch[1];
            op.erase(remove_if(op.begin(), op.end(), ::isspace), op.end());
            if (op == "==" || op == "=") { num_hclauses += 2; }

            else if (op == ">=") {
                num_hclauses++;
            }
            else {
                cout << "operation " << op << " not supported. Use >= or == instead." << endl;
                exit(-1);
            }

            string left = formulaMatch.prefix();
            string right = formulaMatch.suffix();
            double right_tmp = stod(right);
            if (right_tmp - floor(right_tmp) > 1e-6) {
                std::cout << "rhs not int." << right_tmp << std::endl;
                exit(-1);
            }

            vector<int> coefs;
            vector<int> indices;
            int neg_count;
            parse_left(left, coefs, indices, neg_count);
            for (auto index: indices) {
                if (index > num_vars) {
                    num_vars = index;
                }
            }
        } else {
            cout << "operation sign not found." << endl;
            exit(-1);
        }
        constraint.clear();
    }

    num_clauses = num_hclauses + num_sclauses;
    num_vars++;
#ifdef DEBUG
    cout << "read num_clauses = " << num_clauses << endl;
#endif
}

void parse_soft_clauses(ifstream& infile, int& c)
{
    string line;
    string coef_str;
    string index_str;
    num_sclauses = 0;
    int total_soft_weight = 0;

    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        if (line.substr(0,4) == "min:") { line = line.substr(4); }
        smatch match;
        string::const_iterator search_start(line.begin());
        while (regex_search(search_start, line.cend(), match, TERM_REGEX)) {
            coef_str = match[1];
            index_str = match[2];
            coef_str.erase(remove_if(coef_str.begin(), coef_str.end(), ::isspace), coef_str.end());
            index_str.erase(remove_if(index_str.begin(), index_str.end(), ::isspace), index_str.end());

            auto coef = stoi(coef_str); // checked INT32 limit
            auto index = stoi(index_str.substr(1));
            search_start = match.suffix().first;

            /* build soft clause */
            clause_lit_count[c] = 1;
            org_clause_weight[c] = abs(coef);
            clause_true_lit_thres[c] = 1;
            total_soft_weight += org_clause_weight[c];

            // create new clause
            clause_lit[c] = new lit[2];

            clause_lit[c][0].clause_num = c;
            clause_lit[c][0].var_num = index;
            clause_lit[c][0].weight = 1;

            if (coef > 0) {
                clause_lit[c][0].sense = false;
            } else {
                clause_lit[c][0].sense = true;
                soft_fixed_cost += coef;
            }
            var_lit_count[clause_lit[c][0].var_num]++;

            // end of clause
            clause_lit[c][1].var_num = 0;
            clause_lit[c][1].clause_num = -1;
            clause_lit[c][1].weight = 0;
            clause_coef_sum[c] = 1;

            soft_clause_num_index[num_sclauses++] = c;
            c++;
        }

        if (line.find(';') != string::npos) {
            break;
        }
    }
    top_clause_weight = total_soft_weight + 1;
}

void parse_hard_clauses(ifstream& infile, int& c)
{
    string line;
    string constraint;
    num_hclauses = 0;
    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        constraint += line + " ";

        /* read until ; */
        if (line.find(';') == string::npos) { continue; }

        /* split */
        smatch formulaMatch;
        if (regex_search(constraint, formulaMatch, EQUALITY_REGEX)) {
            string op = formulaMatch[1];
            string left = formulaMatch.prefix();
            string right = formulaMatch.suffix();
            double right_tmp = stod(right);
            if (right_tmp - floor(right_tmp) > 1e-6) {
                std::cout << "rhs not int." << right_tmp << std::endl;
                exit(-1);
            }
            op.erase(remove_if(op.begin(), op.end(), ::isspace), op.end());

            if (op == "==" || op == "=") {
                build_eq_constraint(c, left, stoi(right));
            } else {
                build_ge_constarint(c, left, stoi(right));
            }
        }
        // clear and read next constraint
        constraint.clear();
    }
}

void build_instance(const char *filename)
{
    int i, v, c;
    path = filename;
    ifstream infile(filename);
    if (!infile)
    {
        cout << "c the input filename " << filename << " is invalid, please input the correct filename." << endl;
        exit(-1);
    }

    /*** build problem data structures of the instance ***/

    // parse_instance_scale(infile);
    count_soft_clauses(infile);
    check_operations(infile);

    allocate_memory();

    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_coef_sum[c] = 0;
        clause_true_lit_thres[c] = 1;
        clause_lit[c] = nullptr;
    }

    for (v = 0; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v] = nullptr;
        var_neighbor[v] = nullptr;
    }

    long long total_soft_weight = 0;
    int cur_weight;

    /* back to beginning */
    infile.clear();
    infile.seekg(0, ios::beg);

    /* read clauses */
    c = 0;
    parse_soft_clauses(infile, c);
    parse_hard_clauses(infile, c);
    infile.close();

	// creat var literal arrays
    build_var_lit(true);

    if (use_presolve) {
        Presolve pre;
        pre.Run();
        build_var_lit(false);
    }
    if (avg_neighbor_lit < 1e+7)
    {
        build_neighbor_relation();
        flip_ptr = flip_with_neighbor;
	} else {
		flip_ptr = flip_no_neighbor;
	}

    best_soln_feasible = 0;
	opt_unsat_weight = top_clause_weight;
	local_opt_unsat_weight = top_clause_weight;
    read_finish_time = get_runtime();
    cout << path << " read complete" << endl;
}


bool check_soln_in_org_instance(const char *filename) {
    string line;
    string coef_str;
    string index_str;
    int obj_value = 0;
    ifstream infile(filename);
    if (!infile) {
        cout << "c the input filename " << filename << " is invalid, please input the correct filename." << endl;
        exit(-1);
    }
    /*** skip ***/
    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        if (line.substr(0,4) == "min:") { line = line.substr(4); }

        smatch match;
        string::const_iterator search_start(line.begin());
        while (regex_search(search_start, line.cend(), match, TERM_REGEX)) {
            coef_str = match[1];
            index_str = match[2];
            coef_str.erase(remove_if(coef_str.begin(), coef_str.end(), ::isspace), coef_str.end());
            index_str.erase(remove_if(index_str.begin(), index_str.end(), ::isspace), index_str.end());

            auto coef = stoi(coef_str); // checked INT32 limit
            auto index = stoi(index_str.substr(1));
            obj_value += coef * best_soln[index];
            search_start = match.suffix().first;
        }

        if (line.find(';') != string::npos) {
            break;
        }
    }

    if (obj_value != opt_unsat_weight + soft_fixed_cost) {
        ofstream ofile("error.log");
        ofile << path << ": " << "obj mismatch " << obj_value << " (org) != (soln) "
              << opt_unsat_weight + soft_fixed_cost << endl;
        cout << path << ": " << "obj mismatch " << obj_value << " (org) != (soln) "
             << opt_unsat_weight + soft_fixed_cost << endl;
        ofile.close();
        return false;
    }

    // check hard clause satisfiability

    string constraint;
    while (getline(infile, line)) {
        if (line[0] == '*') { continue; }
        constraint += line + " ";

        /* read until ; */
        if (line.find(';') == string::npos) { continue; }

        /* split */
        smatch formulaMatch;
        if (regex_search(constraint, formulaMatch, EQUALITY_REGEX)) {
            string op = formulaMatch[1];
            string left = formulaMatch.prefix();
            string right = formulaMatch.suffix();
            op.erase(remove_if(op.begin(), op.end(), ::isspace), op.end());
            vector<int> coefs;
            vector<int> indices;
            int neg_count = 0;
            parse_left(left, coefs, indices, neg_count);
            int sum_left = 0;
            for (int i = 0; i < coefs.size(); ++i) {
                sum_left += coefs[i] * best_soln[indices[i]];
            }
            if (op == "==" || op == "=") {
                if (sum_left != stoi(right)) {
                    ofstream ofile("error.log");
                    ofile << path << ": " << "equation unsat: " << endl;
                    ofile << constraint << endl;
                    ofile.close();
                    cout << path << ": " << "equation unsat: " << endl;
                    cout << constraint << endl;
                    for (int i = 0; i < coefs.size(); ++i) {
                        cout << best_soln[indices[i]] << " ";
                    }
                    cout << endl;
                    return false;
                }
            } else if (op == ">=") {
                if (sum_left < stoi(right)) {
                    ofstream ofile("error.log");
                    ofile << path << ": " << "inequality unsat: " << endl;
                    ofile << constraint << endl;
                    ofile.close();
                    cout << path << ": " << "inequality unsat: " << endl;
                    cout << constraint << endl;
                    return false;
                }
            }
        }
        // clear and read next constraint
        constraint.clear();
    }
    return true;
}

void build_var_lit(bool malloc)
{
    //create var literal arrays
    int v, c, i;
    long long tmp_lit_num = 0;
    if (malloc) {
        for (v = 0; v <= num_vars; ++v)
        {
            var_lit[v] = new lit[var_lit_count[v] + 1];
        }
    }

    for (v = 0; v <= num_vars; ++v)
    {
        tmp_lit_num += var_lit_count[v];
        var_lit_count[v] = 0; //reset to 0, for build up the array
    }
    avg_neighbor_lit = double(tmp_lit_num -num_sclauses )/ (num_vars-num_sclauses+1);

    //scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            if (v == 0) { continue; }
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
    }
    for (v = 1; v <= num_vars; ++v) {
        var_lit[v][var_lit_count[v]].clause_num = -1;
    }
}

void init_local_search(vector<int> &init_solution)
{
	int v, c;
	int i, j;

	local_soln_feasible = 0;

	// Initialize clause information
	for (i = 0; i < num_hclauses; i++)
	{
		c = hard_clause_num_index[i];
		unit_weight[c] = 1;
        tuned_degree_unit_weight[c] = double(unit_weight[c]) / avg_clause_coe[c];
        hard_clause_weight_sum += tuned_degree_unit_weight[c];
	}
	// round
	double tmp_avg_soft_clause_weight = 0.0;
	tmp_avg_soft_clause_weight = round(double(top_clause_weight - 1) / num_sclauses);
	if (tmp_avg_soft_clause_weight < 1)
	 	tmp_avg_soft_clause_weight = 1;
	for (i = 0; i < num_sclauses; i++)
	{
		c = soft_clause_num_index[i];
		tune_soft_clause_weight[c] = double(org_clause_weight[c] / tmp_avg_soft_clause_weight);
        unit_weight[c] = initsoftw;
	}

	// init solution
	init_assignment_ptr(init_solution);

	// init stacks
	hard_unsat_nb = 0;
	hardunsat_stack_fill_pointer = 0;
	softunsat_stack_fill_pointer = 0;

	/* figure out sat_count, sat_var, soft_unsat_weight and init unsat_stack */
	soft_unsat_weight = 0;

	for (i = 0; i < num_hclauses; i++)
	{
		c = hard_clause_num_index[i];
		sat_count[c] = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				sat_count[c] += clause_lit[c][j].weight;
				sat_var[c] = clause_lit[c][j].var_num;
			}
		}
		if (sat_count[c] < clause_true_lit_thres[c])
		{
			unsat(c);
		}
	}
	for (i = 0; i < num_sclauses; i++)
	{
		c = soft_clause_num_index[i];
		sat_count[c] = 0;

		if (cur_soln[clause_lit[c][0].var_num] == clause_lit[c][0].sense)
		{
			sat_count[c] += clause_lit[c][0].weight;
			sat_var[c] = clause_lit[c][0].var_num;
		}
		else
		{
			soft_unsat_weight += (clause_true_lit_thres[c] - sat_count[c]) * org_clause_weight[c];
			unsat(c);
		}
	}

	/*figure out score*/
	init_score_multi();
	
	// init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++)
	{
		if (hscore[v] + sscore[v] > double_tol)
		{
			already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			mypush(v, goodvar_stack);
		}
		else
			already_in_goodvar_stack[v] = -1;
	}
    local_optima_thres = init_local_optima_thres;
    final_attempt_state = 0;
    propagate_record->clear();
}

int pick_var()
{
	int i, v, r, c, l, w;
	int best_var;
	lit *p;

	if (goodvar_stack_fill_pointer > 0)
	{
		if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
			return goodvar_stack[rand() % goodvar_stack_fill_pointer];

		if (goodvar_stack_fill_pointer < hd_count_threshold)
		{
			best_var = goodvar_stack[0];
			for (i = 1; i < goodvar_stack_fill_pointer; ++i)
			{
				v = goodvar_stack[i];
				if (hscore[v] + sscore[v] > hscore[best_var] + sscore[best_var])
					best_var = v;
				else if (hscore[v] + sscore[v] == hscore[best_var] + sscore[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
		else
		{
			r = rand() % goodvar_stack_fill_pointer;
			best_var = goodvar_stack[r];

			for (i = 1; i < hd_count_threshold; ++i)
			{
				r = rand() % goodvar_stack_fill_pointer;
				v = goodvar_stack[r];
				if (hscore[v] + sscore[v] > hscore[best_var] + sscore[best_var])
					best_var = v;
				else if (hscore[v] + sscore[v] == hscore[best_var] + sscore[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
	}

    if (use_runtime_unit_propagate && local_optima_count > local_optima_thres) {
        local_optima_count = 0;
        systematic_search();
        return 0;
    }

    update_clause_weights();
    local_optima_count++;
    auto flipvar = select_var_after_update_weight_ptr();
    time_stamp[flipvar] = step;
    flip_ptr(flipvar);
    return 0;
}

void update_goodvarstack(int flipvar)
{
	int v;

	// remove the variables no longer goodvar in goodvar_stack
	for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	{
		v = goodvar_stack[index];
		if (hscore[v] + sscore[v] <= double_tol)
		{
			int top_v = mypop(goodvar_stack);
			goodvar_stack[index] = top_v;
			already_in_goodvar_stack[top_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
	}

	// add goodvar
	for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
	{
		v = var_neighbor[flipvar][i];
		if (hscore[v] + sscore[v] > double_tol)
		{
			if (already_in_goodvar_stack[v] == -1 && time_stamp[v] < step)
			{
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
	}
}

void flip_with_neighbor(int flipvar)
{
	int i, v, c;
	int index;
	lit *clause_c;
	int weight;
	int gap;

	double org_flipvar_score = hscore[flipvar];
	double org_sscore = sscore[flipvar];
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	flip_update_score_multi(flipvar);

	// update information of flipvar
	hscore[flipvar] = -org_flipvar_score;
	sscore[flipvar] = -org_sscore;
	update_goodvarstack(flipvar);
}

void flip_no_neighbor(int flipvar)
{
	int i, v, c;
	int index;
	lit *clause_c;
	int weight;
	int gap;

	double org_flipvar_score = hscore[flipvar];
	double org_sscore = sscore[flipvar];
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	flip_update_score_no_neighbor_multi(flipvar);

	// update information of flipvar
	hscore[flipvar] = -org_flipvar_score;
	sscore[flipvar] = -org_sscore;
	if (already_in_goodvar_stack[flipvar] != -1)
	{
		int top_v = mypop(goodvar_stack);
		goodvar_stack[already_in_goodvar_stack[flipvar]] = top_v;
		already_in_goodvar_stack[top_v] = already_in_goodvar_stack[flipvar];
		already_in_goodvar_stack[flipvar] = -1;
	}
}

template<class T> void print_array(ofstream& ofs, vector<T>& vec, string name) {
    if (!vec.empty()) {
        ofs << "    \"" << name << "\": [" << vec[0];
        for (int i = 1; i < vec.size(); ++i) {
            ofs << ", " << vec[i];
        }
        ofs << "]," << endl;
    } else {
        ofs << "    \"" << name << "\": []," << endl;
    }
}

void print_best_solution()
{
    if (best_soln_feasible && !check_soln_in_org_instance(path.c_str())) {
        exit(-1);
    }
    string name;
    istringstream iss(path);
    string token;
    while (getline(iss, token, '/')) {
        name += token;
        name += "_";
    }
    ofstream ofs("raw/" + name + ".json", ios::app);
    ofs << endl;
    ofs << "    {" << endl;
    ofs << R"(        "name": ")" << path << "\"," << endl;
    if (best_soln_feasible == 0) {
        ofs << R"(        "obj": "-", )" << endl;
        ofs << R"(        "opt_time": "-", )" << endl;
    } else {
        ofs << R"(        "obj": )" << opt_unsat_weight + soft_fixed_cost << "," << endl;
        ofs << R"(        "opt_time": )" << opt_time << "," << endl;
    }
    print_array(ofs, opt_soln_update_history, "opt_soln_update_history");
    print_array(ofs, opt_soln_update_time, "opt_soln_update_time");

    ofs << R"(        "num_local_optima": )" << num_propagate_called << "," << endl;
    ofs << R"(        "num_backtrack": )" << num_backtrack << "," << endl;
    ofs << R"(        "final_attempt": )" << final_attempt_attempt << "," << endl;
    ofs << R"(        "final_attempt_succ": )" << final_attempt_success << "," << endl;
    ofs << R"(        "propagate_succ_len": )" << propagate_success_len << "," << endl;
    ofs << R"(        "propagate_fail_len": )" << propagate_fail_len << "," << endl;
    ofs << R"(        "tries": )" << tries << "," << endl;
    ofs << R"(        "total_step": )" << total_step << endl;
    ofs << "    }";
    ofs.close();
}

void update_best_soln()
{
    local_soln_feasible = 1;
    if (local_opt_unsat_weight > soft_unsat_weight)
    {
        local_opt_unsat_weight = soft_unsat_weight;
        max_flips = step + max_non_improve_flip;
    }
    if (soft_unsat_weight < opt_unsat_weight)
    {
        opt_time = get_runtime();
        opt_unsat_weight = soft_unsat_weight;
        for (int v = 1; v <= num_vars; ++v)
            best_soln[v] = cur_soln[v];
        opt_soln_update_history.push_back(opt_unsat_weight + soft_fixed_cost);
        opt_soln_update_time.push_back(opt_time);
        final_attempt_state = 0;
        std::cout << opt_unsat_weight + soft_fixed_cost << std::endl;
    }
    best_soln_feasible = 1;
   // check_soln_in_org_instance(path.c_str());
    if (opt_unsat_weight == 0) {
        print_best_solution();
        exit(0);
    }
}

void local_search(vector<int> &init_solution, const char *inputfile)
{

    imply_table.Init();
    if (proved_unsat) {
        return;
    }
	for (tries = 0; tries < 10000000; ++tries)
	{
        /*if (start_try_at_best_soln && best_soln_feasible) {
            init_solution.resize(num_vars + 1);
            for (int v = 0; v <= num_vars; ++v) {
                init_solution[v] = best_soln[v];
            }
        }*/
        init_local_search(init_solution);
        max_flips = 10000000;
        step_for_propagate = 100000;
        for (step = 1; step < max_flips || goodvar_stack_fill_pointer > 0; ++step)
		{
			if (hard_unsat_nb == 0)
			{
                local_soln_feasible = 1;
				best_soln_feasible = 1;
				if (soft_unsat_weight < opt_unsat_weight)
				{
                    update_best_soln();
            	}
            }

			int flipvar = pick_var();
            if (flipvar != 0) {
                time_stamp[flipvar] = step;
                flip_ptr(flipvar);
                total_step++;
            }
            // check_new_score();

            if (step >= max_flips - 1 && use_final_attempt && goodvar_stack_fill_pointer == 0 && final_attempt_state < final_attempt_looptime && best_soln_feasible) {
                final_attempt_state++;
                final_attempt_attempt++;
                max_flips += 10000;
                for (int v = 1; v <= num_vars; ++v) {
                    if (cur_soln[v] != best_soln[v]) {
                        flip_ptr(v);
                        time_stamp[v] = step;
                    }
                }
                systematic_search();
            }
        }

    }
}

void check_softunsat_weight()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count++;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) // verify hard clauses
			{
				continue;
			}
			else
			{
				verify_unsat_weight += org_clause_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);
			}
		}
	}

	if (verify_unsat_weight != soft_unsat_weight)
	{
		cout << step << endl;
		cout << "verify unsat weight is" << verify_unsat_weight << " and soft unsat weight is " << soft_unsat_weight << endl;
	}
	// return 0;
}

bool verify_sol()
{
	cout << "c start verification" << endl;
	int c, j, flag;
	long long verify_unsat_weight = 0;
	long long real_min_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		if (org_clause_weight[c] != top_clause_weight)
		{
			if (clause_lit[c][0].sense == 0)
			{
				real_min_weight += org_clause_weight[c] * best_soln[clause_lit[c][0].var_num];
			}
			else
			{
				real_min_weight -= org_clause_weight[c] * best_soln[clause_lit[c][0].var_num];
			}
		}
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count += clause_lit[c][j].weight;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) // verify hard clauses
			{
				// output the falsified clause under the assignment
				cout << "c Error: hard clause " << c << " is falsified" << endl;

				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;
				return 0;
			}
			else
			{
				verify_unsat_weight += org_clause_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);

			}
		}
	}

	if (verify_unsat_weight == opt_unsat_weight)
	{
		cout << "c realmin: " << real_min_weight << endl;
		return 1;
	}
	else
	{
		cout << "c Error: find opt=" << opt_unsat_weight << ", but verified opt=" << verify_unsat_weight << endl;
	}
	return 0;
}

void simple_print()
{
	if (best_soln_feasible == 1)
	{
		if (verify_sol() == 1)
			cout << opt_unsat_weight << '\t' << opt_time << endl;
		else
			cout << "solution is wrong " << endl;
	}
	else
		cout << -1 << '\t' << -1 << endl;
}

void increase_weights()
{
	int i, c, v;
	int weight;
	int flag = 0;

	for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
	{
		flag = 1;
		c = hardunsat_stack[i];
        unit_weight[c] += h_inc;
        tuned_degree_unit_weight[c] = double(unit_weight[c]) / avg_clause_coe[c];
        hard_clause_weight_sum += double(h_inc / tuned_degree_unit_weight[c]);
		update_weight_score_multi(c);
	}
	// increase all soft clause weights
	if (0 == hard_unsat_nb)
	{
        soft_clause_weight_increased += 1;
		for (i = 0; i < num_sclauses; i++)
		{
			c = soft_clause_num_index[i];
			unit_weight[c] += s_inc;
			v = clause_lit[c][0].var_num;
            if (v == 0) { continue; }
			if (clause_lit[c][0].sense != cur_soln[v])
			{
				sscore[v] += s_inc * tune_soft_clause_weight[c];
				if (hscore[v] + sscore[v] > double_tol && already_in_goodvar_stack[v] == -1)
				{
					already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
					mypush(v, goodvar_stack);
				}
			}
			else
			{
				sscore[v] -= s_inc * tune_soft_clause_weight[c];
				if (already_in_goodvar_stack[v] != -1 && hscore[v] + sscore[v] <= 0)
				{
					int top_v = mypop(goodvar_stack);
					goodvar_stack[already_in_goodvar_stack[v]] = top_v;
					already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
					already_in_goodvar_stack[v] = -1;
				}
			}
		}
	}
}

void update_clause_weights()
{
	increase_weights();
}

void unsat(int clause)
{
	if (org_clause_weight[clause] == top_clause_weight) // hard
	{
		index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
		mypush(clause, hardunsat_stack);
		hard_unsat_nb++;
	}
	else // soft
	{
		index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
		mypush(clause, softunsat_stack);
		// soft_unsat_weight += org_clause_weight[clause];
	}
}

void sat(int clause)
{
	int index, last_unsat_clause;

	if (org_clause_weight[clause] == top_clause_weight)
	{

		last_unsat_clause = mypop(hardunsat_stack);
		index = index_in_hardunsat_stack[clause];
		hardunsat_stack[index] = last_unsat_clause;
		index_in_hardunsat_stack[last_unsat_clause] = index;

		hard_unsat_nb--;
	}
	else
	{
		last_unsat_clause = mypop(softunsat_stack);
		index = index_in_softunsat_stack[clause];
		softunsat_stack[index] = last_unsat_clause;
		index_in_softunsat_stack[last_unsat_clause] = index;

		// soft_unsat_weight -= org_clause_weight[clause];
	}
}

void check_new_score()
{
	long long tem_score = 0;
	long long tem_sscore = 0;
	int sense, c, v, i;
	int weight;
	for (v = 1; v <= num_vars; v++)
	{
		tem_score = 0;
		tem_sscore = 0;
		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			sense = var_lit[v][i].sense;
			weight = var_lit[v][i].weight;
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_score += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_score -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_score -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
			else
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_sscore += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_sscore -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_sscore -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
		}
		if (tem_score != hscore[v] || tem_sscore != sscore[v])
		{

			cout << "score is worng in variable " << v << endl;
			cout << "tem_score is " << tem_score << endl;
			cout << "score function is " << hscore[v] << endl;
			cout << "flip num is " << step << endl;

			for (i = 0; i < var_lit_count[v]; ++i)
			{
				c = var_lit[v][i].clause_num;
				sense = var_lit[v][i].sense;
				weight = var_lit[v][i].weight;
				cout << c << " ";
			}
			cout << endl;
			exit(0);
			break;
		}
	}

	int tem_unsat_softweight = 0;
	for (int i = 0; i < num_clauses; ++i)
	{
		if (org_clause_weight[i] == top_clause_weight)
			continue;
		if (sat_count[i] < clause_true_lit_thres[i])
		{
			tem_unsat_softweight += (clause_true_lit_thres[i] - sat_count[i]);
		}
	}
	if (tem_unsat_softweight != soft_unsat_weight)
	{
		cout << "verify softunsat weight wrong " << endl;
		exit(0);
	}
}

void start_timing()
{
	times(&start_time);
}

double get_runtime()
{
	struct tms stop;
	times(&stop);
	return (double)(stop.tms_utime - start_time.tms_utime + stop.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK);
}

void Presolve::Init()
{
    checkList_.resize(num_clauses + 1, 0);
    indexInCheckList_.resize(num_clauses + 1, -1);
    checkListFillPointer_ = 0;
    for (int i = 0; i < num_hclauses; ++i) {
        int c = hard_clause_num_index[i];
        indexInCheckList_[c] = checkListFillPointer_;
        checkList_[checkListFillPointer_++] = c;
    }
}

void Presolve::CheckConstraint(int c)
{
    if (org_clause_weight[c] != top_clause_weight) {
        if (clause_true_lit_thres[c] <= 0 || clause_coef_sum[c] < clause_true_lit_thres[c]) {
            // clause is unsatisfiable or already satisfied: remove this clause
            if (clause_coef_sum[c] < clause_true_lit_thres[c] && clause_true_lit_thres[c] > 0) {
                soft_fixed_cost += org_clause_weight[c];
            }
            clause_true_lit_thres[c] = 0;
            sat_count[c] = 0;
            clause_coef_sum[c] = 0;
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                clause_lit[c][i].weight = 0;
            }
        }
    } else { // hard clause

        // clause_coef_sum will be updated in "fix_var" step
        if (clause_coef_sum[c] < clause_true_lit_thres[c]) {
            proved_unsat = true;
            return;
        }
        if (clause_true_lit_thres[c] <= 0) {
            clause_true_lit_thres[c] = 0;
            sat_count[c] = 0;
            clause_coef_sum[c] = 0;
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                clause_lit[c][i].weight = 0;
                // caution: corresponding var_lit[v][j] remains weight != 0
            }
        } else {
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                auto &l = clause_lit[c][i];
                if (IsFixed(l.var_num)) { continue; }
                if (clause_coef_sum[c] - l.weight < clause_true_lit_thres[c]) {
                    FixVarByTerm(l);
                }
            }
        }
    }

    auto index = indexInCheckList_[c];
    auto tail = checkList_[--checkListFillPointer_];
    checkList_[index] = tail;
    indexInCheckList_[tail] = index;
    indexInCheckList_[c] = -1;
}

void Presolve::Run()
{
    // fix vars found in build_instance()
    for (int v = 1; v <= num_vars; ++v) {
        if (IsFixed(v)) {
            FixVarBySense(v, fixed_sense[v]);
        }
    }
    if (avg_neighbor_lit < 1e7) {
        while (checkListFillPointer_ > 0 && !proved_unsat) {
            CheckConstraint(checkList_[checkListFillPointer_ - 1]);
        }
        if (proved_unsat) {return;}
        for (int c = 0; c < num_clauses; ++c) {
            Saturate(c);
            Divide(c);
            ToCardinal(c);
            ToPlanted(c);
        }
    }
    ClearZeroCoefTerms();
    for (int i = num_hclauses - 1; i >= 0; --i) {
        int c = hard_clause_num_index[i];
        if (clause_true_lit_thres[c] <= 0) {
            // remove from hclause
            hard_clause_num_index[i] = hard_clause_num_index[--num_hclauses];
        }
    }
}

void Presolve::FixVarBySense(int v, bool sense)
{
    // record fix
    fixed_sense[v] = static_cast<int>(sense);
    // substitute
    for (int i = 0; i < var_lit_count[v]; ++i) {
        auto& l = var_lit[v][i];
        auto c = l.clause_num;
        if (clause_true_lit_thres[c] <= 0) {
            // important:
            // if some clause is naturally satisfied,
            // clause_coef_sum[c] = 0 and clause_lit[c][i].weight = 0
            // but corresponding var_lit[v][j] != 0
            // so the rest operation on l must be skipped
            continue;
        }
        clause_coef_sum[c] -= l.weight;
        if (l.sense == sense) {
            clause_true_lit_thres[c] -= l.weight;
        } else {
            if (indexInCheckList_[c] == -1) {
                indexInCheckList_[c] = checkListFillPointer_;
                checkList_[checkListFillPointer_++] = l.clause_num;
            }
        }
        l.weight = 0;
    }
}

void Presolve::FixVarByTerm(lit& t)
{
    FixVarBySense(t.var_num, t.sense);
}

void Presolve::Saturate(int c)
{
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        if (IsFixed(clause_lit[c][i].var_num)) { continue; }
        if (clause_lit[c][i].weight > clause_true_lit_thres[c]) {
            clause_coef_sum[c] += clause_true_lit_thres[c] - clause_lit[c][i].weight;
            clause_lit[c][i].weight = clause_coef_sum[c];
        }
    }
}

void Presolve::Divide(int c)
{
    int res = clause_lit[c][0].weight;
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        if (IsFixed(clause_lit[c][i].var_num)) { continue; }
        auto coef = clause_lit[c][i].weight;
        if (coef == 0) { continue; }
        res = gcd(res, coef);
        if (res <= 1) break;
    }

    if (res <= 1) return;
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        clause_lit[c][i].weight /= res;
    }
    auto& degree = clause_true_lit_thres[c];
    if (degree % res == 0) {
        degree /= res;
    } else {
        degree /= res;
        degree++;
    }
    clause_coef_sum[c] /= res;
}

void Presolve::ToCardinal(int c)
{
    int64_t smallSum = 0;
    int64_t largeSum = 0;
    size_t i = 0;
    size_t j = 0;
    auto& degree = clause_true_lit_thres[c];
    vector<int> coefs;
    coefs.reserve(clause_lit_count[c]);
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        auto coef = clause_lit[c][i].weight;
        if (coef == 0 || IsFixed(clause_lit[c][i].var_num)) { continue; }
        coefs.push_back(coef);
    }
    sort(coefs.begin(), coefs.end(), greater<int>());
    size_t n = coefs.size();

    while (smallSum < degree && i < n) {
        smallSum += coefs[n - i - 1];
        i++;
    }
    while (largeSum < degree && j < n) {
        largeSum += coefs[j];
        j++;
    }
    if (i != j) { return; }

    for (int i = 0; i < clause_lit_count[c]; ++i) {
        auto& coef = clause_lit[c][i].weight;
        if (coef != 0) {
            coef = 1;
        }
    }
    degree = j;
    clause_coef_sum[c] = n;
}

void Presolve::ToPlanted(int c)
{
    // e.g. +31 x1 +16 x2 + 8 x3 +4 x4 +2 x5 +1 x6 >= 31
    // x1 = 0 -> x2,...,x6 = 1
    // x1 = 1 -> x2,...,x6 free
    // which is equivalent to :
    // +5 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 >= 5
    auto& coefSum = clause_coef_sum[c];
    int minCoef = coefSum;
    int maxCoef = 0;
    int termNum = 0; // number of non-zero terms
    auto& degree = clause_true_lit_thres[c];
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        auto coef = clause_lit[c][i].weight;
        if (coef == 0 || IsFixed(clause_lit[c][i].var_num)) { continue; }
        termNum++;
        if (coef < minCoef) { minCoef = coef; }
        if (coef > maxCoef) { maxCoef = coef; }
    }
    if (termNum <= 2) { return; }

    bool visitedMaxCoefFlag = false;
    if (maxCoef >= degree && coefSum - maxCoef >= degree && coefSum - minCoef - maxCoef < degree) {
        for (int i = 0; i < clause_lit_count[c]; ++i) {
            auto& coef = clause_lit[c][i].weight;
            if (coef == 0 || IsFixed(clause_lit[c][i].var_num)) { continue; }
            if (!visitedMaxCoefFlag && coef == maxCoef) {
                coef = termNum - 1;
                visitedMaxCoefFlag = true;
            } else {
                coef = 1;
            }
        }
        degree = termNum - 1;
        coefSum = 2 * degree;
    }
}

void Presolve::ClearZeroCoefTerms()
{
    int eraseCount = 0;

    // clear in constr
    for (int c = 0; c < num_clauses; ++c) {
        eraseCount = 0;
        for (int i = 0; i < clause_lit_count[c]; ++i) {
            if (clause_lit[c][i].weight == 0 || IsFixed(clause_lit[c][i].var_num)) {
                eraseCount++;
            }
        }
        if (eraseCount == 0) { continue; }
        ClearZeroCoefTermInConstr(c, eraseCount);
    }
}

void Presolve::ClearZeroCoefTermInConstr(int c, int eraseCount)
{
    // vec is constr.data or object.data
    // promise that number of deleted item > 0
    int fillPointer = 0;
    if (clause_true_lit_thres[c] <= 0 || clause_lit_count[c] == eraseCount) {
        clause_lit[c][fillPointer].weight = 1;
        clause_lit[c][fillPointer].var_num = 0;
        fillPointer++;
    } else {
        for (int i = 0; i < clause_lit_count[c]; ++i) {
            if (clause_lit[c][i].weight == 0 || IsFixed(clause_lit[c][i].var_num)) { continue; }
            if (i == fillPointer) { fillPointer++; continue; }
            clause_lit[c][fillPointer].weight = clause_lit[c][i].weight;
            clause_lit[c][fillPointer].var_num = clause_lit[c][i].var_num;
            clause_lit[c][fillPointer].sense = clause_lit[c][i].sense;
            fillPointer++;
        }
    }
    clause_lit[c][fillPointer].weight = 0;
    clause_lit[c][fillPointer].var_num = 0;
    clause_lit[c][fillPointer].clause_num = -1;
    clause_lit_count[c] = fillPointer;
}

ImplicationTable::ImplicationTable(size_t v) :
    var_num(v),
    table(2 * v + 2),
    flag(2 * v + 2, imply_level::empty){

}

void ImplicationTable::Init() {
    for (int c = 0; c < num_clauses; ++c) {
        if (org_clause_weight[c] != top_clause_weight) { continue; }
        if (clause_lit[c][0].weight != 1) { continue; }
        if (clause_true_lit_thres[c] == clause_lit_count[c] - 1) { continue; }
        AddClique(c);
    }
}

void ImplicationTable::AddClique(int c) {
    for (int i = 0; i < clause_lit_count[c]; ++i) {
        int index = to_index(clause_lit[c][i].var_num, clause_lit[c][i].sense);
        auto iter = clique_index.find(index);
        if (iter != clique_index.end()) {
            iter->second.push_back(c);       // index in clique n
        } else {
            clique_index.insert(make_pair(index, vector<uint32_t>()));
            clique_index[index].reserve(var_lit_count[clause_lit[c][i].var_num]);
            clique_index[index].push_back(c);
        }
    }
}

vector<var_with_sense>& ImplicationTable::GetCliqueLevel(int v, int sense) {
    auto posIndex = to_index(v, sense);
    auto negIndex = to_index(v, 1 - sense);
    if (flag[posIndex] != imply_level::empty) { return table[posIndex]; }
    if (clique_index.find(negIndex) == clique_index.end()) {
        flag[posIndex] = imply_level::clique;
        return table[posIndex];
    }
    table[posIndex].reserve(num_vars);
    // record what is in table
    vector<int> visited(num_vars + 1, -1);
    visited[v] = 1 - sense;
    for (auto c: clique_index[negIndex]) {
        for (int i = 0; i < clause_lit_count[c]; ++i) {
            auto& l2 = clause_lit[c][i];
            if (visited[l2.var_num] == -1) {
                table[posIndex].emplace_back(l2.var_num, l2.sense);
                visited[l2.var_num] = l2.sense;
            } else if (visited[l2.var_num] == l2.sense) { continue; }
            else {
                table[posIndex].clear();
                table[posIndex].emplace_back(l2.var_num, 1-sense);
                flag[posIndex] = imply_level::formula;
                table[posIndex].shrink_to_fit();
                return table[posIndex];
            }
        }
    }
    table[posIndex].shrink_to_fit();
    flag[posIndex] = imply_level::clique;

    return table[posIndex];
}


vector<var_with_sense>& ImplicationTable::GetClauseLevel(int v, int sense) {
    auto posIndex = to_index(v, sense);
    if (flag[posIndex] == imply_level::clause || flag[posIndex] == imply_level::formula) { return table[posIndex]; }
    table[posIndex].reserve(num_vars);
    // record what is in table
    vector<int> visited(num_vars + 1, -1);

    for (int i = 0; i < var_lit_count[v]; ++i) {
        auto &l = var_lit[v][i];
        // cout << l.var_num << ' ' << l.sense << ' ' << l.weight << ' ' << l.clause_num << endl;
        if (l.sense == sense) { continue; }
        auto c = l.clause_num;
        if (org_clause_weight[c] != top_clause_weight) { continue; }
        if (clause_coef_sum[c] - l.weight < clause_true_lit_thres[c]) {
            // means v == sense conflicts
            table[posIndex].clear();
            table[posIndex].emplace_back(l.var_num, l.sense);
            flag[posIndex] = imply_level::formula;
            table[posIndex].shrink_to_fit();
            return table[posIndex];
        }

        for (int j = 0; j < clause_lit_count[c]; ++j) {
            auto &l2 = clause_lit[c][j];
            if (l2.var_num == l.var_num) { continue; }
            if (l2.weight == 0) { continue; }
            // given ranked by coef


            if (l.weight + l2.weight <= clause_coef_sum[c] - clause_true_lit_thres[c]) { break; }
            // now we find -l -> l2
            if (visited[l2.var_num] == -1) {
                table[posIndex].emplace_back(l2.var_num, l2.sense);
                visited[l2.var_num] = l2.sense;
            } else if (visited[l2.var_num] == l2.sense) {
                continue;
            } else {
                // -l -> l
                table[posIndex].clear();
                table[posIndex].emplace_back(l.var_num, l.sense);
                flag[posIndex] = imply_level::formula;
                table[posIndex].shrink_to_fit();
                return table[posIndex];
            }
        }
    }

    table[posIndex].shrink_to_fit();
    flag[posIndex] = imply_level::clause;

    return table[posIndex];
}

vector<var_with_sense> &ImplicationTable::GetFormulaLevel(int v, int sense) {
    //double get_start_time = get_runtime();
    auto index = to_index(v, sense);
    auto negIndex = to_index(v, 1 - sense);
    if (flag[index] == imply_level::formula) { return table[index]; }
    int malloc_var_size = num_vars + 1;
    vector<var_with_sense> dfs;
    dfs.reserve(malloc_var_size);
    vector<int> visited(malloc_var_size, -1);

    auto& UPvector = GetClauseLevel(v, sense);
    // UPvector -> sense and visited
    for (auto& vws: UPvector) {
        // check if newSense conflict with previous sense
        auto newSense = vws.sense;
        if (visited[vws.id] != -1) {
            if (visited[vws.id] != newSense) {
                UPvector.clear();
                UPvector.emplace_back(v, 1-sense);
                UPvector.shrink_to_fit();
                flag[index] = imply_level::formula;
                //time += get_runtime() - get_start_time;
                return UPvector;
            } else { continue; }
        } else {
            dfs.push_back(vws);
            visited[vws.id] = newSense;
        }
    }
    while (!dfs.empty()) {
        auto searchVWS = dfs.back();
        dfs.pop_back();

        int searchV = searchVWS.id;
        auto& searchUP = GetClauseLevel(searchVWS.id, searchVWS.sense);

        // visit children of searchVWS
        for (auto& childVWS: searchUP) {
            auto newSense = childVWS.sense;
            if (visited[childVWS.id] != -1) {
                if (visited[childVWS.id] != newSense) {
                    UPvector.emplace_back(v, 1-sense);
                    UPvector.shrink_to_fit();
                    flag[index] = imply_level::formula;
                    //time += get_runtime() - get_start_time;
                    return UPvector;
                } else {
                    continue;
                }
            } else {
                dfs.push_back(childVWS);
                visited[childVWS.id] = newSense;
            }
        }
    }

    // fill in unit propagation vector
    UPvector.clear();
    UPvector.reserve(num_vars);
    for (int vid = 1; vid <= num_vars; ++vid) {
        if (vid == v) { continue; }
        if (visited[vid] == -1) { continue; }
        UPvector.emplace_back(vid, visited[vid]);
    }
    UPvector.shrink_to_fit();
    flag[index] = imply_level::formula;
    //time += get_runtime() - get_start_time;
    return UPvector;
}

vector<var_with_sense>& ImplicationTable::GetTable(int v, int sense) {
    if (num_vars > 100000) {
        return imply_table.GetClauseLevel(v, sense);
    } else {
        return imply_table.GetFormulaLevel(v, sense);
    }
}

vector<var_with_sense>& ImplicationTable::GetCurrTable(int v, int sense) {
    return table[to_index(v, sense)];
}


void print_opb() {
    ofstream ofs("test.opb", ios::trunc);
    ofs << "* #variable= " << num_vars << " ";
    ofs << " #constraint= " << num_clauses << endl;

    ofs << "min: ";
    for (int i = 0; i < num_sclauses; ++i) {
        int c = soft_clause_num_index[i];
        int coef = int(org_clause_weight[c]);
        if (clause_lit[c][0].var_num == 0) {
            continue;
        }
        if (clause_lit[c][0].sense) {
            ofs << "-" << coef << " ";
        } else {
            ofs << "+" << coef << " ";
        }
        ofs << "x" << clause_lit[c][0].var_num << " ";
    }
    ofs << ";" << endl;

    for (int i = 0; i < num_hclauses; ++i) {
        int c = hard_clause_num_index[i];
        int negSum = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j) {
            auto t = clause_lit[c][j];
            if (t.var_num == 0) { continue; }
            if (t.sense) {
                ofs << "+" << t.weight << " ";
            } else {
                ofs << "-" << t.weight << " ";
                negSum += t.weight;
            }
            ofs << "x" << t.var_num << " ";
        }
        ofs << ">= " << clause_true_lit_thres[c] - negSum << " ";
        ofs << ";" << endl;
    }
    ofs.close();
}

void print_features() {
    int len_up_clause = 0;
    int len_up_formula = 0;
    int var_up_cnt = 0;
    int num_var_in_up = 0;
    vector<bool> var_in_binary_clause(num_vars+1, false);

    for (int v = 1; v <= num_vars; ++v) {
        if (fixed_sense[v] >= 0) { continue; }
        auto& up_true = imply_table.GetClauseLevel(v, true);
        auto& up_false = imply_table.GetClauseLevel(v, false);
        if (!up_true.empty()) {
            num_var_in_up++;
            len_up_clause += up_true.size();
        }
        if (!up_false.empty()) {
            num_var_in_up++;
            len_up_clause += up_false.size();
        }
    }

    for (int v = 1; v <= num_vars; ++v) {
        if (fixed_sense[v] >= 0) { continue; }
        auto& up_true = imply_table.GetFormulaLevel(v, true);
        auto& up_false = imply_table.GetFormulaLevel(v, false);
        len_up_formula += up_true.size() + up_false.size();
    }

    ofstream ofile("features.json", ios::app);
    ofile << "{" << endl;
    ofile << "\t \"name\": \"" << path << "\"," << endl;
    ofile << "\t \"num_vars\": " << num_vars << "," << endl;
    ofile << "\t \"num_clauses\": " << num_clauses << "," << endl;
    ofile << "\t \"fixed_cost\": " << soft_fixed_cost << "," << endl;
    ofile << "\t \"len_up_clause\": " << len_up_clause << "," << endl;
    ofile << "\t \"len_up_formula\": " << len_up_formula << "," << endl;
    ofile << "\t \"num_var_in_up\": " << num_var_in_up << "," << endl;
    ofile << "}," << endl;
}
