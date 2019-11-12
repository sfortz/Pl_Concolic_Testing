
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>

#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif


/**
   \brief Create an enumeration data type.
*/
void enum_example() {
    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);
    Z3_sort fruit;
    Z3_symbol name = Z3_mk_string_symbol(ctx, "fruit");
    Z3_symbol enum_names[3];
    Z3_func_decl enum_consts[3];
    Z3_func_decl enum_testers[3];
    Z3_ast apple, orange, banana, fruity;
    Z3_ast ors[3];

    printf("\nenum_example\n");
    LOG_MSG("enum_example");

    enum_names[0] = Z3_mk_string_symbol(ctx,"apple");
    enum_names[1] = Z3_mk_string_symbol(ctx,"banana");
    enum_names[2] = Z3_mk_string_symbol(ctx,"orange");

    fruit = Z3_mk_enumeration_sort(ctx, name, 3, enum_names, enum_consts, enum_testers);

    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[0]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[1]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[2]));

    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[0]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[1]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[2]));

    apple  = Z3_mk_app(ctx, enum_consts[0], 0, 0);
    banana = Z3_mk_app(ctx, enum_consts[1], 0, 0);
    orange = Z3_mk_app(ctx, enum_consts[2], 0, 0);

    /* Apples are different from oranges */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, apple, orange)), true);

    /* Apples pass the apple test */
    prove(ctx, s, Z3_mk_app(ctx, enum_testers[0], 1, &apple), true);

    /* Oranges fail the apple test */
    prove(ctx, s, Z3_mk_app(ctx, enum_testers[0], 1, &orange), false);
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_app(ctx, enum_testers[0], 1, &orange)), true);

    fruity = mk_var(ctx, "fruity", fruit);

    /* If something is fruity, then it is an apple, banana, or orange */
    ors[0] = Z3_mk_eq(ctx, fruity, apple);
    ors[1] = Z3_mk_eq(ctx, fruity, banana);
    ors[2] = Z3_mk_eq(ctx, fruity, orange);

    prove(ctx, s, Z3_mk_or(ctx, 3, ors), true);

    /* delete logical context */
    del_solver(ctx, s);
    Z3_del_context(ctx);
}

/**
   \brief Create a list datatype.
*/
void list_example() {
    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);
    Z3_sort int_ty, int_list;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;
    Z3_ast nil, l1, l2, x, y, u, v, fml, fml1;
    Z3_ast ors[2];


    printf("\nlist_example\n");
    LOG_MSG("list_example");

    int_ty = Z3_mk_int_sort(ctx);

    int_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "int_list"), int_ty,
                               &nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);

    nil = Z3_mk_app(ctx, nil_decl, 0, 0);
    l1 = mk_binary_app(ctx, cons_decl, mk_int(ctx, 1), nil);
    l2 = mk_binary_app(ctx, cons_decl, mk_int(ctx, 2), nil);

    /* nil != cons(1, nil) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, l1)), true);

    /* cons(2,nil) != cons(1, nil) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, l1, l2)), true);

    /* cons(x,nil) = cons(y, nil) => x = y */
    x = mk_var(ctx, "x", int_ty);
    y = mk_var(ctx, "y", int_ty);
    l1 = mk_binary_app(ctx, cons_decl, x, nil);
	l2 = mk_binary_app(ctx, cons_decl, y, nil);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", int_list);
    v = mk_var(ctx, "v", int_list);
    l1 = mk_binary_app(ctx, cons_decl, x, u);
	l2 = mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons_decl, 1, &u);
    prove(ctx, s, Z3_mk_or(ctx, 2, ors), true);

    /* occurs check u != cons(x,u) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
    fml1 = Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, head_decl, u), mk_unary_app(ctx, tail_decl, u)));
    fml = Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &u), fml1);
    printf("Formula %s\n", Z3_ast_to_string(ctx, fml));
    prove(ctx, s, fml, true);

    prove(ctx, s, fml1, false);

    /* delete logical context */
    del_solver(ctx, s);
    Z3_del_context(ctx);
}

/**
   \brief Create a binary tree datatype.
*/
void tree_example() {
    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);
    Z3_sort cell;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
    Z3_ast nil, l1, l2, x, y, u, v, fml, fml1;
    Z3_symbol head_tail[2] = { Z3_mk_string_symbol(ctx, "car"), Z3_mk_string_symbol(ctx, "cdr") };
    Z3_sort sorts[2] = { 0, 0 };
    unsigned sort_refs[2] = { 0, 0 };
    Z3_constructor nil_con, cons_con;
    Z3_constructor constructors[2];
    Z3_func_decl cons_accessors[2];
    Z3_ast ors[2];

    printf("\ntree_example\n");
    LOG_MSG("tree_example");

    nil_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil"), Z3_mk_string_symbol(ctx, "is_nil"), 0, 0, 0, 0);
    cons_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons"), Z3_mk_string_symbol(ctx, "is_cons"), 2, head_tail, sorts, sort_refs);
    constructors[0] = nil_con;
    constructors[1] = cons_con;

    cell = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "cell"), 2, constructors);

    Z3_query_constructor(ctx, nil_con, 0, &nil_decl, &is_nil_decl, 0);
    Z3_query_constructor(ctx, cons_con, 2, &cons_decl, &is_cons_decl, cons_accessors);
    car_decl = cons_accessors[0];
    cdr_decl = cons_accessors[1];

    Z3_del_constructor(ctx,nil_con);
    Z3_del_constructor(ctx,cons_con);


    nil = Z3_mk_app(ctx, nil_decl, 0, 0);
    l1 = mk_binary_app(ctx, cons_decl, nil, nil);
    l2 = mk_binary_app(ctx, cons_decl, l1, nil);

    /* nil != cons(nil, nil) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, l1)), true);

    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", cell);
    v = mk_var(ctx, "v", cell);
    x = mk_var(ctx, "x", cell);
    y = mk_var(ctx, "y", cell);
    l1 = mk_binary_app(ctx, cons_decl, x, u);
    l2 = mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons_decl, 1, &u);
    prove(ctx, s, Z3_mk_or(ctx, 2, ors), true);

    /* occurs check u != cons(x,u) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
    fml1 = Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, car_decl, u), mk_unary_app(ctx, cdr_decl, u)));
    fml = Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &u), fml1);
    printf("Formula %s\n", Z3_ast_to_string(ctx, fml));
    prove(ctx, s, fml, true);

    prove(ctx, s, fml1, false);

    /* delete logical context */
    del_solver(ctx, s);
    Z3_del_context(ctx);


}

/**
   \brief Create a forest of trees.

   forest ::= nil | cons(tree, forest)
   tree   ::= nil | cons(forest, forest)
*/

void forest_example() {
    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);
    Z3_sort tree, forest;
    Z3_func_decl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
    Z3_func_decl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
    Z3_ast nil1, nil2, t1, t2, t3, t4, f1, f2, f3, l1, l2, x, y, u, v;
    Z3_symbol head_tail[2] = { Z3_mk_string_symbol(ctx, "car"), Z3_mk_string_symbol(ctx, "cdr") };
    Z3_sort sorts[2] = { 0, 0 };
    unsigned sort_refs[2] = { 0, 0 };
    Z3_constructor nil1_con, cons1_con, nil2_con, cons2_con;
    Z3_constructor constructors1[2], constructors2[2];
    Z3_func_decl cons_accessors[2];
    Z3_ast ors[2];
    Z3_constructor_list clist1, clist2;
    Z3_constructor_list clists[2];
    Z3_symbol sort_names[2] = { Z3_mk_string_symbol(ctx, "forest"), Z3_mk_string_symbol(ctx, "tree") };

    printf("\nforest_example\n");
    LOG_MSG("forest_example");

    /* build a forest */
    nil1_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil1"), Z3_mk_string_symbol(ctx, "is_nil1"), 0, 0, 0, 0);
    sort_refs[0] = 1; /* the car of a forest is a tree */
    sort_refs[1] = 0;
    cons1_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons1"), Z3_mk_string_symbol(ctx, "is_cons1"), 2, head_tail, sorts, sort_refs);
    constructors1[0] = nil1_con;
    constructors1[1] = cons1_con;

    /* build a tree */
    nil2_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil2"), Z3_mk_string_symbol(ctx, "is_nil2"),0, 0, 0, 0);
    sort_refs[0] = 0; /* both branches of a tree are forests */
    sort_refs[1] = 0;
    cons2_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons2"), Z3_mk_string_symbol(ctx, "is_cons2"),2, head_tail, sorts, sort_refs);
    constructors2[0] = nil2_con;
    constructors2[1] = cons2_con;

    clist1 = Z3_mk_constructor_list(ctx, 2, constructors1);
    clist2 = Z3_mk_constructor_list(ctx, 2, constructors2);

    clists[0] = clist1;
    clists[1] = clist2;

    Z3_mk_datatypes(ctx, 2, sort_names, sorts, clists);
    forest = sorts[0];
    tree = sorts[1];

    Z3_query_constructor(ctx, nil1_con, 0, &nil1_decl, &is_nil1_decl, 0);
    Z3_query_constructor(ctx, cons1_con, 2, &cons1_decl, &is_cons1_decl, cons_accessors);
    car1_decl = cons_accessors[0];
    cdr1_decl = cons_accessors[1];

    Z3_query_constructor(ctx, nil2_con, 0, &nil2_decl, &is_nil2_decl, 0);
    Z3_query_constructor(ctx, cons2_con, 2, &cons2_decl, &is_cons2_decl, cons_accessors);
    car2_decl = cons_accessors[0];
    cdr2_decl = cons_accessors[1];

    Z3_del_constructor_list(ctx, clist1);
    Z3_del_constructor_list(ctx, clist2);
    Z3_del_constructor(ctx,nil1_con);
    Z3_del_constructor(ctx,cons1_con);
    Z3_del_constructor(ctx,nil2_con);
    Z3_del_constructor(ctx,cons2_con);

    nil1 = Z3_mk_app(ctx, nil1_decl, 0, 0);
    nil2 = Z3_mk_app(ctx, nil2_decl, 0, 0);
    f1 = mk_binary_app(ctx, cons1_decl, nil2, nil1);
    t1 = mk_binary_app(ctx, cons2_decl, nil1, nil1);
    t2 = mk_binary_app(ctx, cons2_decl, f1, nil1);
    t3 = mk_binary_app(ctx, cons2_decl, f1, f1);
    t4 = mk_binary_app(ctx, cons2_decl, nil1, f1);
    f2 = mk_binary_app(ctx, cons1_decl, t1, nil1);
    f3 = mk_binary_app(ctx, cons1_decl, t1, f1);


    /* nil != cons(nil,nil) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil1, f1)), true);
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil2, t1)), true);


    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", forest);
    v = mk_var(ctx, "v", forest);
    x = mk_var(ctx, "x", tree);
    y = mk_var(ctx, "y", tree);
    l1 = mk_binary_app(ctx, cons1_decl, x, u);
    l2 = mk_binary_app(ctx, cons1_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil1_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons1_decl, 1, &u);
    prove(ctx, s, Z3_mk_or(ctx, 2, ors), true);

    /* occurs check u != cons(x,u) */
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    /* delete logical context */
    del_solver(ctx, s);
    Z3_del_context(ctx);
}



/**
   \brief Create a binary tree datatype of the form
        BinTree ::=   nil
                    | node(value : Int, left : BinTree, right : BinTree)
*/
void binary_tree_example() {
    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);
    Z3_sort cell;
    Z3_func_decl
        nil_decl, /* nil : BinTree   (constructor) */
        is_nil_decl, /* is_nil : BinTree -> Bool (tester, return true if the given BinTree is a nil) */
        node_decl, /* node : Int, BinTree, BinTree -> BinTree  (constructor) */
        is_node_decl, /* is_node : BinTree -> Bool (tester, return true if the given BinTree is a node) */
        value_decl,  /* value : BinTree -> Int  (accessor for nodes) */
        left_decl,   /* left : BinTree -> BinTree (accessor for nodes, retrieves the left child of a node) */
        right_decl;  /* right : BinTree -> BinTree (accessor for nodes, retrieves the right child of a node) */
    Z3_symbol node_accessor_names[3] = { Z3_mk_string_symbol(ctx, "value"), Z3_mk_string_symbol(ctx, "left"), Z3_mk_string_symbol(ctx, "right") };
    Z3_sort   node_accessor_sorts[3] = { Z3_mk_int_sort(ctx), 0, 0 };
    unsigned  node_accessor_sort_refs[3] = { 0, 0, 0 };
    Z3_constructor nil_con, node_con;
    Z3_constructor constructors[2];
    Z3_func_decl node_accessors[3];

    printf("\nbinary_tree_example\n");
    LOG_MSG("binary_tree_example");

    /* nil_con and node_con are auxiliary datastructures used to create the new recursive datatype BinTree */
    nil_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil"), Z3_mk_string_symbol(ctx, "is-nil"), 0, 0, 0, 0);
    node_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "node"), Z3_mk_string_symbol(ctx, "is-cons"),
                                 3, node_accessor_names, node_accessor_sorts, node_accessor_sort_refs);
    constructors[0] = nil_con;
    constructors[1] = node_con;

    /* create the new recursive datatype */
    cell = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "BinTree"), 2, constructors);

    /* retrieve the new declarations: constructors (nil_decl, node_decl), testers (is_nil_decl, is_cons_del), and
       accessors (value_decl, left_decl, right_decl */
    Z3_query_constructor(ctx, nil_con, 0, &nil_decl, &is_nil_decl, 0);
    Z3_query_constructor(ctx, node_con, 3, &node_decl, &is_node_decl, node_accessors);
    value_decl = node_accessors[0];
    left_decl  = node_accessors[1];
    right_decl = node_accessors[2];

    /* delete auxiliary/helper structures */
    Z3_del_constructor(ctx, nil_con);
    Z3_del_constructor(ctx, node_con);

    /* small example using the recursive datatype BinTree */
    {
        /* create nil */
        Z3_ast nil = Z3_mk_app(ctx, nil_decl, 0, 0);
        /* create node1 ::= node(10, nil, nil) */
        Z3_ast args1[3] = { mk_int(ctx, 10), nil, nil };
        Z3_ast node1    = Z3_mk_app(ctx, node_decl, 3, args1);
        /* create node2 ::= node(30, node1, nil) */
        Z3_ast args2[3] = { mk_int(ctx, 30), node1, nil };
        Z3_ast node2    = Z3_mk_app(ctx, node_decl, 3, args2);
        /* create node3 ::= node(20, node2, node1); */
        Z3_ast args3[3] = { mk_int(ctx, 20), node2, node1 };
        Z3_ast node3    = Z3_mk_app(ctx, node_decl, 3, args3);

        /* prove that nil != node1 */
        prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, node1)), true);

        /* prove that nil = left(node1) */
        prove(ctx, s, Z3_mk_eq(ctx, nil, mk_unary_app(ctx, left_decl, node1)), true);

        /* prove that node1 = right(node3) */
        prove(ctx, s, Z3_mk_eq(ctx, node1, mk_unary_app(ctx, right_decl, node3)), true);

        /* prove that !is-nil(node2) */
        prove(ctx, s, Z3_mk_not(ctx, mk_unary_app(ctx, is_nil_decl, node2)), true);

        /* prove that value(node2) >= 0 */
        prove(ctx, s, Z3_mk_ge(ctx, mk_unary_app(ctx, value_decl, node2), mk_int(ctx, 0)), true);
    }

    /* delete logical context */
    del_solver(ctx, s);
    Z3_del_context(ctx);
}


int main() {
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif
    list_example();
    tree_example();
    forest_example();
    binary_tree_example();
    return 0;
}
