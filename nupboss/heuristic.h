#ifndef _HEURISTIC_H
#define _HEURISTIC_H
#include "basis_pms.h"

void init_score_multi();


extern void (*flip_ptr)(int flipvar);
void flip_with_neighbor(int flipvar);
void flip_no_neighbor(int flipvar);

void flip_update_score_multi(int flipvar);
void flip_update_score_no_neighbor_multi(int flipvar);

void update_weight_score_multi(int c);

extern int (*select_var_after_update_weight_ptr)();
bool systematic_search();
int select_var_after_update_weight_1();
int select_var_after_update_weight_2();
double get_avg_imply_score(int v);

bool backtrack_impl(int best_var, double last_punish);
void flip_up(int v, map<long long, long long>& former_time_stamp, FlipRecord* record);
void flip_clique(int best_var);

void handle_backtrack_result(bool flag);
extern double (*soft_var_greedy_ptr)(int v);
extern double (*hard_var_greedy_ptr)(int v);
double var_greedy_hscore(int v);
double var_greedy_sscore(int v);
double var_greedy_score(int v);
double GetPunish();

#endif