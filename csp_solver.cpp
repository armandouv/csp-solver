//
// Created by armandouv on 22/05/22.
//

#include <bits/stdc++.h>

using namespace std;




// Type definitions

/**
 * {variable_name, domain}
 */
template<typename T>
using Variable_set = map<string, set<T>>;

template<typename T>
using Consistency_checker = function<bool(const T &a, const T &b)>;

using Edge = pair<string, string>;
//using Triplet = tuple<string, string, string>;

/**
 * First: Scope (variables involved in the constraint)
 * Second: Function that determines whether two variables are consistent with the constraint.
 */
template<typename T>
using Constraint = pair<Edge, Consistency_checker<T>>;

template<typename T>
using Constraint_adj_list = unordered_map<string, unordered_map<string, Consistency_checker<T>>>;

enum Problem_status {
    SOLVED,
    UNSOLVABLE,
    PENDING
};




// Utilities

template<typename T>
Problem_status check_status(const Variable_set<T> &variables) {
    for (const auto &[_, domain]: variables) {
        if (domain.empty()) return UNSOLVABLE;
        else if (domain.size() > 1) return PENDING;
    }
    return SOLVED;
}


template<typename T>
void build_adj_list(const Variable_set<T> &variables, const vector<Constraint<T>> &constraints,
                    Constraint_adj_list<T> &adj_list) {
    for (const auto &[variable_name, _] : variables) {
        adj_list[variable_name];
    }

    for (const auto &[edge, checker]: constraints) {
        adj_list[edge.first][edge.second] = checker;
        adj_list[edge.second][edge.first] = checker;
    }
}

template<typename T>
void print_vars(Variable_set<T> variables) {
    for (const auto &var: variables) {
        cout << var.first << ": { ";
        for (const auto &val: var.second)
            cout << val << " ";
        cout << "}" << endl;
    }
    cout << endl << endl;
}

template<typename T>
bool solved_status(const Variable_set<T> &variables) {
    cout << "Final state (solved):" << endl;
    print_vars(variables);
    return true;
}

template<typename T>
bool unsolvable_status(const Variable_set<T> &variables) {
    cout << "Unsolvable" << endl;
    return false;
}




// Constraint propagation algorithms

// AC3
template<typename T>
bool revise(Variable_set<T> &variables, const Consistency_checker<T> checker, const string &xi, const string &xj) {
    bool revised{false};

    set<T> to_delete;

    for (const auto &x: variables[xi]) {
        bool possible = false;

        for (const auto &y: variables[xj]) {
            if (!checker(x, y)) continue;

            possible = true;
            break;
        }

        if (!possible) {
            to_delete.insert(x);
            revised = true;
        }
    }

    for (const auto &del: to_delete)
        variables[xi].erase(del);

    return revised;
}

template<typename T>
Problem_status ac3(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list) {
    queue<Edge> arcs;
    for (const auto &[source, neighbors_map]: adj_list) {
        for (const auto &[neighbor, _]: neighbors_map)
            arcs.push({source, neighbor});
    }

    while (!arcs.empty()) {
        const auto [xi, xj] = arcs.front();
        arcs.pop();

        auto checker = adj_list.at(xi).at(xj);

        if (revise(variables, checker, xi, xj)) {
            if (variables[xi].empty()) return UNSOLVABLE;

            for (const auto &[neighbor, _]: adj_list.at(xi)) {
                if (neighbor == xj) continue;
                arcs.push({neighbor, xi});
            }
        }
    }

    return check_status(variables);
}


// PC-2 (pending)
/*
template<typename T>
bool revise3(Variable_set<T> &variables, const Consistency_checker<T> checker1, const Consistency_checker<T> checker2,
             const string &xi, const string &xk, const string &xj) {
    set<pair<T, T>> to_delete;
    bool revised{false};

    for (const auto &x: variables[xi]) {
        for (const auto &y: variables[xj]) {
            bool possible = false;
            for (const auto &z: variables[xk]) {
                if (!checker1(x, z) || !checker2(z, y)) continue;

                possible = true;
                break;
            }

            if (!possible) {
                to_delete.insert({x, y});
                revised = true;
            }
        }
    }


    for (const auto &del: to_delete) {
        variables[xi].erase(del.first);
        variables[xj].erase(del.second);
    }

    return revised;
}


template<typename T>
Problem_status pc2(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list) {
    queue<Triplet> arcs;
    for (const auto &[source, neighbors_map]: adj_list) {
        for (const auto &[neighbor, _]: neighbors_map) {
            for (const auto &[second_neighbor, tmp_]: adj_list.at(neighbor)) {
                if (second_neighbor == source) continue;
                arcs.push({source, neighbor, second_neighbor});
            }
        }
    }

    while (!arcs.empty()) {
        const auto [xi, xk, xj] = arcs.front();
        arcs.pop();

        auto checker1 = adj_list.at(xi).at(xk);
        auto checker2 = adj_list.at(xk).at(xj);

        if (revise3(variables, checker1, checker2, xi, xk, xj)) {
            if (variables[xi].empty() || variables[xj].empty()) return UNSOLVABLE;

            // TODO: Check original pc2 paper.
            for (const auto &[neighbor, _]: adj_list.at(xi)) {
                if (neighbor == xk) continue;
                arcs.push({neighbor, xi, xk});
                arcs.push({xk, xi, neighbor});
            }

            for (const auto &[neighbor, _]: adj_list.at(xj)) {
                if (neighbor == xk) continue;
                arcs.push({neighbor, xj, xk});
                arcs.push({xk, xj, neighbor});
            }
        }
    }

    return check_status(variables);
}
 */


// Backtracking
template<typename T>
string select_unassigned_variable(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list, map<string, T> &assignment,
                                  set<string> &unassigned) {
    return *unassigned.begin();
}

template<typename T>
vector<T> order_domain_values(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list, map<string, T> &assignment,
        const string &chosen_variable) {
    vector<T> ordered;

    for (const auto &val : variables[chosen_variable]) {
        ordered.push_back(val);
    }

    return ordered;
}

template<typename T>
bool is_consistent(const Constraint_adj_list<T> &adj_list, map<string, T> &assignment,
                   const string &chosen_variable, const T &candidate_val) {
    for (const auto &[variable_name, value] : assignment) {
        if (!adj_list.at(chosen_variable).contains(variable_name))
            continue;

        auto checker = adj_list.at(chosen_variable).at(variable_name);
        if (!checker(candidate_val, value))
            return false;
    }
    return true;
}

template<typename T>
void backtrack(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list, map<string, T> &assignment,
               set<string> &unassigned) {
    if (assignment.size() == variables.size()) return;

    auto chosen = select_unassigned_variable(variables, adj_list, assignment, unassigned);
    unassigned.erase(chosen);
    auto ordered_domain = order_domain_values(variables, adj_list, assignment, chosen);

    for (const auto &val : ordered_domain) {
        if (!is_consistent(adj_list, assignment, chosen, val)) continue;

        assignment[chosen] = val;
        // TODO: Add inference
        backtrack(variables, adj_list, assignment, unassigned);
        if (assignment.size() == variables.size()) return;
        assignment.erase(chosen);
    }

    unassigned.insert(chosen);
}

template<typename T>
map<string, T> backtracking_search(Variable_set<T> &variables, const Constraint_adj_list<T> &adj_list) {
    map<string, T> result;
    set<string> unassigned;
    for (const auto &[var_name, _] : variables)
        unassigned.insert(var_name);

    backtrack(variables, adj_list, result, unassigned);
    return result;
}


/**
 * Updates the variables' domains appropriately until a solution is found.
 * In other words, if one is found, all variables will have singleton domains.
 * Else, at least one will contain an empty domain.
 *
 * @tparam T
 * @param variables
 * @param constraints
 * @return true if a solution was found. Else, return false.
 */
template<typename T>
bool solve_csp(Variable_set<T> &variables, const vector<Constraint<T>> &constraints) {
    cout << "Initial state:" << endl;
    print_vars(variables);

    Constraint_adj_list<T> adj_list;
    build_adj_list(variables, constraints, adj_list);

    auto status = ac3(variables, adj_list);
    if (status == UNSOLVABLE) return unsolvable_status(variables);
    else if (status == SOLVED) return solved_status(variables);
/*
    status = pc2(variables, adj_list);
    if (status == UNSOLVABLE) return unsolvable_status(variables);
    else if (status == SOLVED) return solved_status(variables);
*/
    auto solution = backtracking_search(variables, adj_list);
    if (solution.empty()) return unsolvable_status(variables);

    for (const auto &[variable_name, assigned_value] : solution) {
        variables[variable_name] = { assigned_value };
    }
    return solved_status(variables);
}




// Domain-specific constraints and utilities.
template<typename T>
bool check_diff(const T &a, const T &b) {
    return a != b;
}

vector<Constraint<int>> generate_binary_all_diff(const vector<string> &variable_names) {
    vector<Constraint<int>> constraints;
    auto n = variable_names.size();

    for (auto i = 0; i < n; i++) {
        auto curr_var = variable_names[i];
        for (int j = i + 1; j < n; j++) {
            Edge edge{curr_var, variable_names[j]};
            Constraint<int> new_constraint = make_pair(edge, check_diff<int>);
            constraints.push_back(new_constraint);
        }
    }

    return constraints;
}




// CSP instances

void solve_sudoku() {
    ifstream ifs{"/home/armandouv/Documents/Projects/csp-solver/input/sudoku.in"};
    if (!ifs)
        throw runtime_error("Couldn't open sudoku.in for reading");

    set<int> initial_domain{1, 2, 3, 4, 5, 6, 7, 8, 9};
    Variable_set<int> variables;

    for (char c = 'A'; c <= 'I'; c++) {
        for (int i = 1; i <= 9; i++) {
            char digit;
            ifs >> digit;
            auto var_name = c + to_string(i);

            if (isdigit(digit)) variables[var_name] = {digit - '0'};
            else variables[var_name] = initial_domain;
        }
    }


    vector<Constraint<int>> constraints;
    // Rows all-diff
    for (char c = 'A'; c <= 'I'; c++) {
        vector<string> curr_all_diff;
        for (int i = 1; i <= 9; i++) {
            curr_all_diff.push_back(c + to_string(i));
        }

        auto generated_constraints = generate_binary_all_diff(curr_all_diff);
        for (const auto &constraint: generated_constraints)
            constraints.push_back(constraint);
    }


    // Columns all-diff
    for (int i = 1; i <= 9; i++) {
        vector<string> curr_all_diff;
        for (char c = 'A'; c <= 'I'; c++) {
            curr_all_diff.push_back(c + to_string(i));
        }

        auto generated_constraints = generate_binary_all_diff(curr_all_diff);
        for (const auto &constraint: generated_constraints)
            constraints.push_back(constraint);
    }

    // Squares all-diff
    vector<vector<string>> squares_all_diff(9, vector<string>{});
    for (char c = 'A'; c <= 'I'; c++) {
        int row = c - 'A';
        int square_row = row / 3;

        for (int i = 1; i <= 9; i++) {
            int square_index = (square_row * 3) + ((i - 1) / 3);
            squares_all_diff[square_index].push_back(c + to_string(i));
        }
    }

    for (const auto &all_diff_variables: squares_all_diff) {
        auto generated_constraints = generate_binary_all_diff(all_diff_variables);
        for (const auto &constraint: generated_constraints)
            constraints.push_back(constraint);
    }

    auto solved = solve_csp(variables, constraints);
    if (!solved) return;

    ofstream ofs{"/home/armandouv/Documents/Projects/csp-solver/output/sudoku.out"};
    if (!ofs)
        throw runtime_error("Couldn't open sudoku.out for writing");

    int i = 0;
    for (const auto &var: variables) {
        ofs << *var.second.begin() << (i == 8 ? "\n" : " ");
        i = (i + 1) % 9;
    }
}


void solve_map_coloring() {
    ifstream ifs{"/home/armandouv/Documents/Projects/csp-solver/input/map_coloring.in"};
    if (!ifs)
        throw runtime_error("Couldn't open map_coloring.in for reading");

    set<string> initial_domain{"Red", "Yellow", "Green", "Blue"};
    Variable_set<string> variables;
    set<string> seen_variables;
    vector<Constraint<string>> constraints;

    string line;
    while (getline(ifs, line)) {
        istringstream iss(line);

        string curr_variable;
        iss >> curr_variable;

        variables.insert({curr_variable, initial_domain});
        seen_variables.insert(curr_variable);

        string neighbor;
        while (iss >> neighbor) {
            if (seen_variables.contains(neighbor)) continue;
            constraints.push_back({{curr_variable, neighbor}, check_diff<string>});
        }
    }

    auto solved = solve_csp(variables, constraints);
    if (!solved) return;

    ofstream ofs{"/home/armandouv/Documents/Projects/csp-solver/output/map_coloring.out"};
    if (!ofs)
        throw runtime_error("Couldn't open map_coloring.out for writing");

    for (const auto &var: variables) {
        ofs << var.first << ": " << *var.second.begin() << endl;
    }
}




int main() {
    solve_sudoku();
    solve_map_coloring();
    return 0;
}