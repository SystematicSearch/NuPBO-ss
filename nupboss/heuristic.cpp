#include "heuristic.h"
#include "basis_pms.h"

#include <cmath>
#include <sstream>
#include <algorithm>

bool compare_score_lt(int v1, int v2) {
    if (var_greedy_score(v1) - var_greedy_score(v2) > double_tol) {
        return false;
    } else if (var_greedy_score(v1) - var_greedy_score(v2) < -double_tol) {
        return true;
    } else {
        return time_stamp[v1] > time_stamp[v2];
    }
}

double GetPunish() {
    double curr_punish = 0;
    for (int i = 0; i < hardunsat_stack_fill_pointer; ++i) {
        int c = hardunsat_stack[i];
        curr_punish += GetHClausePunish(c);
    }
    for (int i = 0; i < softunsat_stack_fill_pointer; ++i) {
        int c = softunsat_stack[i];
        curr_punish += GetSClausePunish(c);
    }
    return curr_punish;
}


void init_score_multi()
{
    int sense, weight, v, c;
    for (v = 1; v <= num_vars; v++)
    {
        hscore[v] = 0;
        sscore[v] = 0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            sense = var_lit[v][i].sense;
            weight = var_lit[v][i].weight;

            if (org_clause_weight[c] == top_clause_weight) // hard
            {
                if (sat_count[c] < clause_true_lit_thres[c]) // falsified
                {
                    if (sense != cur_soln[v]) // flip better
                    {
                        hscore[v] += double(tuned_degree_unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight));
                    }
                    else  // flip worse
                    {
                        hscore[v] -= double(tuned_degree_unit_weight[c] * weight);
                    }
                }
                else if (sat_count[c] >= clause_true_lit_thres[c]) // satisfied
                {
                    if (sense == cur_soln[v]) // flip worse
                    {
                        hscore[v] -= double(tuned_degree_unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight));
                    }
                }
            }
            else // soft
            {
                if (sat_count[c] < clause_true_lit_thres[c]) // falsified
                {
                    if (sense != cur_soln[v]) // flip better
                    {
                        sscore[v] += unit_weight[c] * tune_soft_clause_weight[c];
                    }
                    else                                                          // flip worse
                    {
                        sscore[v] -= unit_weight[c] * tune_soft_clause_weight[c];
                    }
                }
                else if (sat_count[c] >= clause_true_lit_thres[c]) // satisfied
                {
                    if (sense == cur_soln[v]) // flip worse
                    {
                        sscore[v] -= unit_weight[c] * tune_soft_clause_weight[c];
                    }
                }
            }
        }
    }
    return;
}

void (*flip_ptr)(int flipvar);
void flip_update_score_multi(int flipvar)
{
    int i, v, c, j;
    int index;
    lit *clause_c;
    int weight;
    int gap = 0;
    double change = 0;
    new_unsat_hard_clause_stack_fill_pointer = 0;

    for (i = 0; i < var_lit_count[flipvar]; ++i)
    {
        c = var_lit[flipvar][i].clause_num;
        clause_c = clause_lit[c];
        weight = var_lit[flipvar][i].weight;
        if (org_clause_weight[c] == top_clause_weight) // hard
        {
            if (cur_soln[flipvar] == var_lit[flipvar][i].sense) // flip better
            {
                if (sat_count[c] + weight < clause_true_lit_thres[c]) // 1. falsified to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            change = double((tuned_degree_unit_weight[c] * (min(gap, clause_lit[c][j].weight) - min(gap - weight, clause_lit[c][j].weight))));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] -= change;
                            }
                        }
                    }
                }
                else if (sat_count[c] < clause_true_lit_thres[c]) // 2. falsified to satisfied; //sat_count[c]+weight > clause_true_lit_thres[c]
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            hscore[v] -= double((tuned_degree_unit_weight[c] * min(gap, clause_lit[c][j].weight)));
                        }
                        else
                        {
                            hscore[v] += double(tuned_degree_unit_weight[c] * (clause_lit[c][j].weight - max(0, gap - weight + clause_lit[c][j].weight)));
                        }
                    }
                    sat(c);
                }
                else // 3. satisfied to satisfied; //sat_count[c]+weight > clause_true_lit_thres[c], sat_count[c] > clause_true_lit_thres[c]
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (max(0, gap + clause_lit[c][j].weight) - max(0, gap - weight + clause_lit[c][j].weight)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] += change;
                            }
                        }
                    }
                }

                sat_count[c] += weight;
            }
            else // flip worse;// cur_soln[flipvar] != cur_lit.sense
            {
                if (sat_count[c] - weight >= clause_true_lit_thres[c]) // 4. satisfied to satisfied
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (max(0, gap + weight + clause_lit[c][j].weight) - max(0, gap + clause_lit[c][j].weight)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] -= change;
                            }
                        }
                    }
                }
                else if (sat_count[c] >= clause_true_lit_thres[c]) // 5. satisfied to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            hscore[v] -= double(tuned_degree_unit_weight[c] * (clause_lit[c][j].weight - max(0, gap + clause_lit[c][j].weight)));
                        }
                        else
                        {
                            hscore[v] += double(tuned_degree_unit_weight[c] * min(clause_lit[c][j].weight, gap + weight));
                        }
                    }
                    unsat(c);
                    new_unsat_hard_clause_stack[new_unsat_hard_clause_stack_fill_pointer++] = c;
                }
                else // 6.  falsified to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (min(clause_lit[c][j].weight, gap + weight) - min(clause_lit[c][j].weight, gap)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] += change;
                            }
                        }
                    }
                }

                sat_count[c] -= weight;

            } // end else
        }
        else // soft
        {
            if (cur_soln[flipvar] == var_lit[flipvar][i].sense) // flip better
            {
                soft_unsat_weight -= org_clause_weight[c];
                sat(c);
                sat_count[c] += weight;
            }
            else // flip worse
            {
                soft_unsat_weight += org_clause_weight[c];
                unsat(c);
                sat_count[c] -= weight;
            } // end else
        }
    }
    return;
}
void flip_update_score_no_neighbor_multi(int flipvar)
{
    int i, v, c, j;
    int index;
    lit *clause_c;
    int weight;
    int gap = 0;
    double change = 0;
    new_unsat_hard_clause_stack_fill_pointer = 0;
    for (i = 0; i < var_lit_count[flipvar]; ++i)
    {
        c = var_lit[flipvar][i].clause_num;
        clause_c = clause_lit[c];
        weight = var_lit[flipvar][i].weight;
        if (org_clause_weight[c] == top_clause_weight) // hard
        {
            if (cur_soln[flipvar] == var_lit[flipvar][i].sense) // flip better
            {
                if (sat_count[c] + weight < clause_true_lit_thres[c]) // 1. falsified to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            change = double((tuned_degree_unit_weight[c] * (min(gap, clause_lit[c][j].weight) - min(gap - weight, clause_lit[c][j].weight))));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] -= change;
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
                else if (sat_count[c] < clause_true_lit_thres[c]) // 2. falsified to satisfied; //sat_count[c]+weight > clause_true_lit_thres[c]
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            hscore[v] -= double((tuned_degree_unit_weight[c] * min(gap, clause_lit[c][j].weight)));
                            if (already_in_goodvar_stack[v] != -1 && hscore[v] + sscore[v] <= 0)
                            {
                                int top_v = mypop(goodvar_stack);
                                goodvar_stack[already_in_goodvar_stack[v]] = top_v;
                                already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
                                already_in_goodvar_stack[v] = -1;
                            }
                        }
                        else
                        {
                            hscore[v] += double(tuned_degree_unit_weight[c] * (clause_lit[c][j].weight - max(0, gap - weight + clause_lit[c][j].weight)));
                            if (hscore[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
                            {
                                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                                mypush(v, goodvar_stack);
                            }
                        }
                    }
                    sat(c);
                }
                else // 3. satisfied to satisfied; //sat_count[c]+weight > clause_true_lit_thres[c], sat_count[c] > clause_true_lit_thres[c]
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (max(0, gap + clause_lit[c][j].weight) - max(0, gap - weight + clause_lit[c][j].weight)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] += change;
                                if (hscore[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
                                {
                                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                                    mypush(v, goodvar_stack);
                                }
                            }
                        }
                    }
                }
                sat_count[c] += weight;
            }
            else // flip worse;// cur_soln[flipvar] != cur_lit.sense
            {
                if (sat_count[c] - weight >= clause_true_lit_thres[c]) // 4. satisfied to satisfied
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (max(0, gap + weight + clause_lit[c][j].weight) - max(0, gap + clause_lit[c][j].weight)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] -= change;
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
                else if (sat_count[c] >= clause_true_lit_thres[c]) // 5. satisfied to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense == cur_soln[v])
                        {
                            hscore[v] -= double(tuned_degree_unit_weight[c] * (clause_lit[c][j].weight - max(0, gap + clause_lit[c][j].weight)));
                            if (already_in_goodvar_stack[v] != -1 && hscore[v] + sscore[v] <= 0)
                            {
                                int top_v = mypop(goodvar_stack);
                                goodvar_stack[already_in_goodvar_stack[v]] = top_v;
                                already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
                                already_in_goodvar_stack[v] = -1;
                            }
                        }
                        else
                        {
                            hscore[v] += double(tuned_degree_unit_weight[c] * min(clause_lit[c][j].weight, gap + weight));
                            if (hscore[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
                            {
                                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                                mypush(v, goodvar_stack);
                            }
                        }
                    }
                    unsat(c);
                    new_unsat_hard_clause_stack[new_unsat_hard_clause_stack_fill_pointer++] = c;
                }
                else // 6.  falsified to falsified
                {
                    gap = clause_true_lit_thres[c] - sat_count[c];
                    for (j = 0; j < clause_lit_count[c]; j++)
                    {
                        v = clause_lit[c][j].var_num;
                        if (v == flipvar)
                        {
                            continue;
                        }
                        if (clause_lit[c][j].sense != cur_soln[v])
                        {
                            change = double(tuned_degree_unit_weight[c] * (min(clause_lit[c][j].weight, gap + weight) - min(clause_lit[c][j].weight, gap)));
                            if (0 == change)
                            {
                                break;
                            }
                            else
                            {
                                hscore[v] += change;
                                if (hscore[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
                                {
                                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                                    mypush(v, goodvar_stack);
                                }
                            }
                        }
                    }
                }

                sat_count[c] -= weight;

            } // end else
        }
        else // soft
        {
            if (cur_soln[flipvar] == var_lit[flipvar][i].sense) // flip better
            {
                soft_unsat_weight -= org_clause_weight[c];
                sat(c);
                sat_count[c] += weight;
            }
            else // flip worse
            {
                soft_unsat_weight += org_clause_weight[c];
                unsat(c);
                sat_count[c] -= weight;
            } // end else
        }
    }
    return;
}

void update_weight_score_multi(int c)
{
    int i = 0, v = 0, weight;
    for (i = 0; i < clause_lit_count[c]; i++)
    {
        weight = clause_lit[c][i].weight;
        v = clause_lit[c][i].var_num;
        if (clause_lit[c][i].sense != cur_soln[v])
        {
            hscore[v] += double(h_inc * min(clause_true_lit_thres[c] - sat_count[c], weight)) / avg_clause_coe[c];
            if (hscore[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
        else
        {
            hscore[v] -= double(h_inc * weight) / avg_clause_coe[c];
            if (already_in_goodvar_stack[v] != -1 && hscore[v] + sscore[v] <= 0)
            {
                int top_v = mypop(goodvar_stack);
                goodvar_stack[already_in_goodvar_stack[v]] = top_v;
                already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
                already_in_goodvar_stack[v] = -1;
            }
        }
    }
    return;
}

int (*select_var_after_update_weight_ptr)();

double (*soft_var_greedy_ptr)(int v);
double (*hard_var_greedy_ptr)(int v);
double var_greedy_hscore(int v)
{
    return hscore[v];
}
double var_greedy_sscore(int v)
{
    return sscore[v];
}
double var_greedy_score(int v)
{
    return hscore[v] + sscore[v];
}

int select_var_after_update_weight_1()
{
    int r, c, i, l, best_var;
    if (hardunsat_stack_fill_pointer > 0)
    {
        int gap;
        c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];

        gap = clause_true_lit_thres[c] - sat_count[c];
        l = 0;
        for (i = 0; i < clause_lit_count[c]; i++)
        {
            if (clause_lit[c][i].sense != cur_soln[clause_lit[c][i].var_num])
            {
                temp_unsat[l].var_num = clause_lit[c][i].var_num;
                temp_unsat[l].weight = clause_lit[c][i].weight;
                l++;
            }
        }

        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
            return temp_unsat[rand() % l].var_num;
    
        int best_weight;
        best_var = temp_unsat[0].var_num;
        best_weight = temp_unsat[0].weight;
        for (i = 1; i < l; i++)
        {
            if (hscore[temp_unsat[i].var_num] + sscore[temp_unsat[i].var_num] > hscore[best_var] + sscore[best_var])
            {
                best_var = temp_unsat[i].var_num;
                best_weight = temp_unsat[i].weight;
            }
            else if (hscore[temp_unsat[i].var_num] + sscore[temp_unsat[i].var_num] == hscore[best_var] + sscore[best_var])
            {
                if (time_stamp[temp_unsat[i].var_num] < time_stamp[best_var])
                {
                    best_var = temp_unsat[i].var_num;
                    best_weight = temp_unsat[i].weight;
                }
            }
        }
        return best_var;
    }
    else
    {
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
            c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
        else
        {
            r = rand() % softunsat_stack_fill_pointer;
            c = softunsat_stack[r];
            for (i = 1; i < hd_count_threshold; i++)
            {
                r = rand() % softunsat_stack_fill_pointer;
                if (hscore[clause_lit[softunsat_stack[r]][0].var_num] + sscore[clause_lit[softunsat_stack[r]][0].var_num] > hscore[clause_lit[c][0].var_num] + sscore[clause_lit[c][0].var_num])
                {
                    c = softunsat_stack[r];
                }
            }
        }
        // c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
        return clause_lit[c][0].var_num;
    }
}
int select_var_after_update_weight_2()
{
    int r, c, i, l, best_var, best_w, temp_l, v, w;

    if (hardunsat_stack_fill_pointer > 0)
    {
        c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        l = 0;
        for (i = 0; i < clause_lit_count[c]; i++)
        {
            if (clause_lit[c][i].sense != cur_soln[clause_lit[c][i].var_num])
            {
                temp_unsat[l].var_num = clause_lit[c][i].var_num;
                temp_unsat[l].weight = clause_lit[c][i].weight;
                l++;
            }
        }
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
        {
            return temp_unsat[rand() % l].var_num;
        }
        else
        {
            v = temp_unsat[0].var_num;
            best_w = hscore[v] + sscore[v];
            temp_l = 0;
            temp_array[temp_l++] = v;
            for (i = 1; i < l; i++)
            {
                v = temp_unsat[i].var_num;
                if (best_w < hscore[v] + sscore[v])
                {
                    temp_l = 0;
                    temp_array[temp_l++] = v;
                    best_w = hscore[v] + sscore[v];
                }
                else if (best_w == hscore[v] + sscore[v] && time_stamp[v] < time_stamp[temp_array[0]])
                {
                    temp_l = 0;
                    temp_array[temp_l++] = v;
                }
                else if (best_w == hscore[v] + sscore[v] && time_stamp[v] == time_stamp[temp_array[0]])
                {
                    temp_array[temp_l++] = v;
                }
            }
            return temp_array[rand() % temp_l];
        }
    }
    else
    {
        c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
        return clause_lit[c][0].var_num;
    }

    return rand() % num_vars + 1;
}

double get_avg_imply_score(int v) {
    int cnt = 1;
    double sum = var_greedy_score(v);
    auto& imply = imply_table.GetTable(v, 1-cur_soln[v]);
    for (auto& l: imply) {
        if (l.sense != cur_soln[l.id]) {
            sum += var_greedy_score(l.id);
            cnt++;
        }
    }
    return sum / cnt;
}

bool systematic_search() {
    bool flag;
    auto scores = CandFilter<int, double, long long>(num_cand_in_propagate);
    int num_visited = 0;
    if (hardunsat_stack_fill_pointer == 0) {
        int rand_start_index = rand() % softunsat_stack_fill_pointer;
        int rand_end_index = rand_start_index + min(hd_count_threshold, softunsat_stack_fill_pointer);
        for (int t = rand_start_index; num_visited < hd_count_threshold && t < rand_end_index; ++t) {
            int c = softunsat_stack[t % softunsat_stack_fill_pointer];
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                auto v = clause_lit[c][i].var_num;
                auto sense = clause_lit[c][i].sense;
                if (sense == cur_soln[v]) { continue; }
                scores.Insert(v, sscore[v], time_stamp[v]); // use soft score
                num_visited++;
            }
        }
    } else {
        int rand_start_index = rand() % hardunsat_stack_fill_pointer;
        int rand_end_index = rand_start_index + min(hd_count_threshold, hardunsat_stack_fill_pointer);
        for (int t = rand_start_index; num_visited < hd_count_threshold && t < rand_end_index; ++t) {
            int c = hardunsat_stack[t % hardunsat_stack_fill_pointer];
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                auto v = clause_lit[c][i].var_num;
                auto sense = clause_lit[c][i].sense;
                if (sense == cur_soln[v]) { continue; }
                scores.Insert(v, var_greedy_score(v), time_stamp[v]); // use greedy score
                num_visited++;
            }
        }
    }
    if (scores.IsEmpty()) { return false; }

    double curr_punish = GetPunish();
    for (int i : scores.itemVec) {
        flag = backtrack_impl(i, curr_punish);
        if (final_attempt_state == 0) {
            num_propagate_called++;
        }
        if (flag) { break; }
        else if (final_attempt_state == 0) {
            num_backtrack++;
        }
    }
    handle_backtrack_result(flag);
    int best_v = scores.itemVec[0];
    double best_score = var_greedy_score(scores.itemVec[0]);
    if (!flag) {
        for (int i: scores.itemVec) {
            double tmp_score = var_greedy_score(i);
            if (tmp_score > best_score) {
                best_score = tmp_score;
                best_v = i;
            }
        }
        time_stamp[best_v] = step;
        flip_ptr(best_v);
    }
    return flag;
}

void handle_backtrack_result(bool flag) {
    if (flag) {
        local_optima_thres = init_local_optima_thres;;
    } else {
        if (local_optima_thres < init_local_optima_thres * local_optima_thres_multiplier) {
            local_optima_thres *= 2;
        }
    }
}

void flip_up(int v, map<long long, long long>& former_time_stamp, FlipRecord* record) {
    auto& UP = imply_table.GetTable(v, 1-cur_soln[v]);
    former_time_stamp[v] = time_stamp[v];
    time_stamp[v] = step;
    flip_ptr(v);
    record->push(v);
    for (auto& vws : UP) {
        int v2 = vws.id;
        if (cur_soln[v2] != vws.sense) {
            former_time_stamp[v2] = time_stamp[v2];
            time_stamp[v2] = step; // avoid being flipped back
            flip_ptr(v2);
            record->push(v2);
            if (use_propagate_size_limit && record->size > propagate_size_limit) {
                break;
            }
        }
    }
}

bool backtrack_impl(int best_var, double last_punish) {
    map<long long, long long> former_time_stamp;
    propagate_record->clear();
    flip_up(best_var, former_time_stamp, propagate_record);
    while (goodvar_stack_fill_pointer > 0) {
        int v = pick_var();
        propagate_record->push(v);
        former_time_stamp[v] = time_stamp[best_var];
        time_stamp[v] = step; // avoid being flipped back
        flip_ptr(v);
        if (hardunsat_stack_fill_pointer == 0 && soft_unsat_weight < opt_unsat_weight) { break; }
    }

    if (propagate_record->size == 0) {
        for (auto& pair: former_time_stamp) {
            auto v = pair.first;
            time_stamp[v] = pair.second;
        }
        while (goodvar_stack_fill_pointer > 0) {
            already_in_goodvar_stack[goodvar_stack[--goodvar_stack_fill_pointer]] = -1;
        }
        return false;
    }
    double punish = GetPunish();
    if (punish + double_tol < last_punish || punish - double_tol < last_punish && propagate_record->size > 1) {
        if (final_attempt_state == 0) {
            propagate_success_len += propagate_record->size;
        }
        count_local_opt_method_bt++;
        for (auto& pair: former_time_stamp) {
            auto v = pair.first;
            if (var_greedy_score(v) > double_tol && already_in_goodvar_stack[v] == -1) {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
        total_step += propagate_record->size;
        propagate_record->clear();
        return true;
    }

    // else failure
    if (final_attempt_state == 0) {
        propagate_fail_len += propagate_record->size;
    }
    while (propagate_record->size > 0) {
        int v = propagate_record->tail();
        propagate_record->remove_tail();
        flip_ptr(v);
    }
    for (auto& pair: former_time_stamp) {
        auto v = pair.first;
        time_stamp[v] = pair.second;
    }
    while (goodvar_stack_fill_pointer > 0) {
        already_in_goodvar_stack[goodvar_stack[--goodvar_stack_fill_pointer]] = -1;
    }

    return false;
}