#!/usr/bin/python
import os
import sys
import re

slc_root = -1;
linear_slc_root = -1;
linear_slc = {};
linear_slc_id=0;
tmp_stmt_lst = [];
sym_tbl = {};
input_variables = {};
adjoint_variables = [];
changed_variables = {};
adjoint_sym_tbl = {};
counter=0;
lst_of_adj_stmts=[];
inside_reverse_section=0;
loop_counting_variables = [];
LINEAR_ARRAY_NAME = 'v';
ast_id = -1;

tmp_dict = {};

def set_reverse_mode():
	global inside_reverse_section;
	inside_reverse_section=1;

def get_reverse_mode():
	global inside_reverse_section;
	return inside_reverse_section;

def define_newname():
	global counter;
	newname = "%s[%d]" % (LINEAR_ARRAY_NAME,counter);             counter+=1;
	adjoint_newname = "%s[%d]" % (LINEAR_ARRAY_NAME,counter);     counter+=1;
	adjoint_variables.append(adjoint_newname);
	adjoint_sym_tbl[newname] = adjoint_newname;
	return newname;


def associate_wt_new_idx(str):
	global sym_tbl;
	global input_variables;
	input_variables[str]=1;
	newname = define_newname();
	sym_tbl[str] = newname;

def get_adjoint_name(v):
	if v not in adjoint_sym_tbl:
		return 'a1_%s' % v;
	else:
		return adjoint_sym_tbl[v];

def common_subexpression(expression_type, op1, op2):
	global tmp_stmt_lst;
	#print "looking for %s with operands %s and %s" % (expression_type, op1, op2);
	for s_id in tmp_stmt_lst:
		node = linear_slc[s_id];
		lhs_id = node[2][0]; lhs = linear_slc[lhs_id];
		rhs_id = node[2][1]; rhs = linear_slc[rhs_id];
		if rhs[0]=='expression' and rhs[1]==expression_type:
			if op2=='':
				rhs_op1=linear_slc[rhs[2][0]][1]; 
				if op1==rhs_op1:
					return lhs[1];
			else:
				rhs_op1=linear_slc[rhs[2][0]][1]; 
				rhs_op2=linear_slc[rhs[2][1]][1]; 
				if op1==rhs_op1 and op2==rhs_op2:
					return lhs[1];
	return -1;

def create_adjoint_assignment(lin_assign_id):
	adjoint_assignment_list = [];
	# Get the GETS node out of the slc data structure
	GETS_node = linear_slc[lin_assign_id];
	lhs = linear_slc[GETS_node[2][0]]; 
	rhs = linear_slc[GETS_node[2][1]]; 
	# RHS can be a memref or an expression:
	if rhs[0]=='expression':
		if rhs[1]=='SIN':
			op1=linear_slc[rhs[2][0]];
			mul_lhs = ('memref', get_adjoint_name(lhs[1]), []);
			cos_operand = ('memref', op1[1], []);
			mul_rhs = ('expression', 'COS', [create_new_linear_slc_node(cos_operand)]);
			adj_rhs = ('expression', 'MUL', [create_new_linear_slc_node(mul_lhs), create_new_linear_slc_node(mul_rhs)]);
			adj_lhs = ('memref', get_adjoint_name(op1[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
		if rhs[1]=='MUL':
			op1=linear_slc[rhs[2][0]];
			op2=linear_slc[rhs[2][1]];
			# With respect to the first operator
			mul_lhs = ('memref', get_adjoint_name(lhs[1]), []);
			mul_rhs = ('memref', op2[1], []);
			adj_rhs = ('expression', 'MUL', [create_new_linear_slc_node(mul_lhs), create_new_linear_slc_node(mul_rhs)]);
			adj_lhs = ('memref', get_adjoint_name(op1[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
			# With respect to the second operator
			mul_lhs = ('memref', op1[1], []);
			mul_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_rhs = ('expression', 'MUL', [create_new_linear_slc_node(mul_lhs), create_new_linear_slc_node(mul_rhs)]);
			adj_lhs = ('memref', get_adjoint_name(op2[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
		if rhs[1]=='ADD':
			op1=linear_slc[rhs[2][0]];
			op2=linear_slc[rhs[2][1]];
			# With respect to the first operator
			adj_lhs = ('memref', get_adjoint_name(op1[1]), []);
			adj_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
			# With respect to the second operator
			adj_lhs = ('memref', get_adjoint_name(op2[1]), []);
			adj_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
	elif rhs[0]=='memref':
		global input_variables;
		# Special case if there is an assignment as v23=C[i][j] |=> a1_C[i][j]+=a1_v23
		if rhs[1] in input_variables and lhs[1] not in input_variables:
			adj_add_lhs = ('memref', get_adjoint_name(rhs[1]), []);
			adj_add_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_add = ('expression', 'ADD', [create_new_linear_slc_node(adj_add_lhs), create_new_linear_slc_node(adj_add_rhs)]);
			adj_lhs = ('memref', get_adjoint_name(rhs[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_add)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
		# Special case if there is an assignment as C[i][j]=v23 |=> a1_v23=a1_C[i][j]; a1_C[i][j]=0;
		elif rhs[1] not in input_variables and lhs[1] in input_variables:
			adj_lhs = ('memref', get_adjoint_name(rhs[1]), []);
			adj_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
			adj_lhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_rhs = ('FLOAT', '0.', []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
		else:
			adj_lhs = ('memref', get_adjoint_name(rhs[1]), []);
			adj_rhs = ('memref', get_adjoint_name(lhs[1]), []);
			adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
			adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
	elif rhs[0]=='INT' or rhs[0]=='FLOAT':
		adj_lhs = ('memref', get_adjoint_name(lhs[1]), []);
		adj_rhs = ('FLOAT', '0.', []);
		adj_GETS = ('GETS', '', [create_new_linear_slc_node(adj_lhs), create_new_linear_slc_node(adj_rhs)]);
		adjoint_assignment_list.append(  create_new_linear_slc_node(adj_GETS)  );
	else:
		print "error: unknown rhs %s." % rhs[0]; sys.exit(1);
	adjoint_node = ('adjoint', '', adjoint_assignment_list);
	GETS_successors = GETS_node[2];
	GETS_successors.append(  create_new_linear_slc_node(adjoint_node)  );
	linear_slc[lin_assign_id] = (GETS_node[0], GETS_node[1], GETS_successors);



def unparse_linearized_slc(of):
	global lst_of_adj_stmts;
	if linear_slc_root==-1:
		print "The root node of linearized slc is not defined."; sys.exit(1);
	of.write('%s = new double [%d];\n' % (LINEAR_ARRAY_NAME,counter));
	of.write('/* forward section */\n');
	unparse_linearized_node(of, linear_slc[linear_slc_root]);
	# Inside of unparse_linearized_node the list of adjoint statements is built and
	# this list must be unparsed now to get the reverse section:
	set_reverse_mode();
	of.write('/* reverse section */\n');
	# Initialize adjoints to zero is not necessary since we do not have += but =
	#for adj in adjoint_variables: of.write('%s=0.;  ' % adj);
	of.write('\n');
	for adjoint_stmt in lst_of_adj_stmts:
		for succ in linear_slc[adjoint_stmt][2]:
			unparse_linearized_node(of, linear_slc[succ]);

def unparse_linearized_node(of, node):
	global lst_of_adj_stmts;
	if node[0]=='GETS':
		# If not in reverse mode store this assignment in list of stmts that are later to be adjoined
		if not get_reverse_mode():  lst_of_adj_stmts.insert(0, node[2][len(node[2])-1]);
		unparse_linearized_node(of, linear_slc[node[2][0]]);
		of.write('=');
		unparse_linearized_node(of, linear_slc[node[2][1]]);
		of.write(';\n');
	elif node[0]=='expression':
		if node[1]=='SIN':
			of.write('sin('); unparse_linearized_node(of, linear_slc[node[2][0]]); of.write(')');
		elif node[1]=='COS':
			of.write('cos('); unparse_linearized_node(of, linear_slc[node[2][0]]); of.write(')');
		elif node[1]=='MUL':
			unparse_linearized_node(of, linear_slc[node[2][0]]);
			of.write('*');
			unparse_linearized_node(of, linear_slc[node[2][1]]);
		elif node[1]=='ADD':
			unparse_linearized_node(of, linear_slc[node[2][0]]);
			of.write('+');
			unparse_linearized_node(of, linear_slc[node[2][1]]);
	elif node[0]=='memref' or node[0]=='INT' or node[0]=='FLOAT':
		of.write('%s' % node[1]);
	else:
		for child_id in node[2]:
			unparse_linearized_node(of, linear_slc[child_id]);

def find_ast_root(of, ast):
	if of is None: return;
	if ast is None: return;
	# Look for first node
	for key in ast:
		if ast[key][0]=='slc': 
			#ast_fs_visitor(of, ast, ast[key], key);
			global slc_root;
			slc_root=key;
			break;

def find_input_variables(ast, node_id):
	node=ast[node_id];
	if node[0]=='GETS':
		global tmp_dict;
		lhs_id = node[2][0];
		rhs_id = node[2][1];
		find_input_variables_in_rhs(ast, rhs_id);
		# Add lhs symbol to list of defined symbols
		tmp_dict[ast[lhs_id][1]] = 1;
	else:
		for child in node[2]:
			find_input_variables(ast, child);

def find_input_variables_in_rhs(ast, node_id):
	global input_variables;
	global tmp_dict;
	node=ast[node_id];
	if node[0]=='memref':
		# If symbol not already in set of input variables and has not been defined yet
		if node[1] not in input_variables and node[1] not in tmp_dict:
			input_variables[node[1]]=1;
	for child in node[2]:
		find_input_variables_in_rhs(ast, child);

def create_linear_slc(ast):
	if slc_root==-1:
		print "Unknown entry node to the ast.";
		sys.exit(1);
	node=ast[slc_root];
	seq_of_stmts_id = node[2][0]; seq_of_stmts=ast[seq_of_stmts_id];
	global counter;
	global sym_tbl;
	global linear_slc;
	linear_slc = {};
	sym_tbl = {};
	counter=0;
	unroll_loops(ast, seq_of_stmts_id);
	# Associate each input variable with an intermediate symbol. Thus all variables get into local memory at the beginning of slc.
	global input_variables;
	for iv in input_variables:
		associate_wt_new_idx(iv);
		lhs = ('memref', sym_tbl[iv], []);
		rhs = ('memref', iv, []);
		assign = ('GETS', '', [create_new_linear_slc_node(lhs), create_new_linear_slc_node(rhs)]);
		create_new_linear_slc_assignment(assign);
	# Assume that we run through sequence of GETS
	for child in seq_of_stmts[2]:
		linearize(ast, child);
	# After linearizing the seq of stmts we assign results back to input values.
	# The symbol table gives the current instance of the variables in the linearized code and
	# the changed variables list shows which variables have to be written back.
	global changed_variables;
	global tmp_stmt_lst;
	global linear_slc_root;
	for sym in changed_variables:
		lhs = ('memref', sym, []);
		rhs = ('memref', sym_tbl[sym], []);
		assign = ('GETS', '', [create_new_linear_slc_node(lhs), create_new_linear_slc_node(rhs)]);
		create_new_linear_slc_assignment(assign);
	seq_of_stmts = ('seq_of_stmts', '', tmp_stmt_lst); tmp_stmt_lst = [];
	slc = ('slc', '', [create_new_linear_slc_node(seq_of_stmts)]);
	linear_slc_root=create_new_linear_slc_node(slc);

def create_new_linear_slc_assignment(assign_tupel):
	global tmp_stmt_lst;
	assign_id = create_new_linear_slc_node(assign_tupel);
	create_adjoint_assignment(assign_id);
	tmp_stmt_lst.append( assign_id );

def create_new_linear_slc_node(node_tupel):
	global linear_slc_id;
	linear_slc[linear_slc_id] = node_tupel;
	rc = linear_slc_id;
	linear_slc_id+=1;
	return rc;

def create_new_ast_node(node_tupel):
	global ast_id;
	ast[ast_id] = node_tupel;
	rc = ast_id;
	ast_id+=1;
	return rc;

def linearize_expression(ast, node_id):
	global tmp_stmt_lst;
	node = ast[node_id];
	if node[1]=='SIN':
		linearize(ast, node[2][0]);
		op1 = ast[node[2][0]]; 
		newname=define_newname();
		lhs = ('memref', newname, []);
		newop1 = ('memref', op1[1], []);
		rhs = ('expression', node[1], [create_new_linear_slc_node(newop1)]);
		assign = ('GETS', '', [create_new_linear_slc_node(lhs), create_new_linear_slc_node(rhs)]);
		create_new_linear_slc_assignment(assign);
		# The former node of type expression is represented by a variable with name newname.
		ast[node_id] = (node[0], newname, node[2]);
	elif node[1]=='MUL' or node[1]=='ADD':
		linearize(ast, node[2][0]);
		linearize(ast, node[2][1]);
		op1 = ast[node[2][0]]; 
		op2 = ast[node[2][1]]; 
		newname=define_newname();
		lhs = ('memref', newname, []);
		newop1 = ('memref', op1[1], []);
		newop2 = ('memref', op2[1], []);
		# Disable common subexpression analysis
		#cse = common_subexpression(node[1], op1[1], op2[1]);
		cse=-1;
		if cse==-1:  # If no common subexpression has been found
			rhs = ('expression', node[1], [create_new_linear_slc_node(newop1), create_new_linear_slc_node(newop2)]);
		else:
			rhs = ('memref', cse, []);
		assign = ('GETS', '', [create_new_linear_slc_node(lhs), create_new_linear_slc_node(rhs)]);
		create_new_linear_slc_assignment(assign);
		# The former node of type expression is represented by a variable with name newname.
		ast[node_id] = (node[0], newname, node[2]);
	else:
		print "error: unhandled type of expression: %s" % (node[1],);
		sys.exit(1);

def linearize(ast, node_id):
	global sym_tbl;
	node = ast[node_id];
	if node[0]=='GETS':
		linearize(ast, node[2][1]);
		lhs_id = node[2][0];
		rhs_id = node[2][1];
		# Associate lhs with new intermediate variable
		sym_tbl[ast[lhs_id][1]]=ast[rhs_id][1];
		# Save that the left hand side variable has been changed to know later which values have to be written back
		global changed_variables;
		changed_variables[ast[lhs_id][1]]=1;
	elif node[0]=='expression':
		linearize_expression(ast, node_id);
	elif node[0]=='memref':
		linearize_memref(ast, node_id);
	elif node[0]=='slc':
		linearize(ast, node[2][0]);
	elif node[0]=='seq_of_stmts':
		for stmt_id in node[2]:
			linearize(ast, stmt_id);
	elif node[0]=='FOR':
		linearize_FOR(ast, node_id);
	elif node[0]=='INT' or node[0]=='FLOAT':
		linearize_CONSTANT(ast, node_id);
	else:
		print "error: unhandled case of node type: %s" % (node[0],);
		sys.exit(1);

def linearize_CONSTANT(ast, node_id):
	linearize_memref(ast, node_id);

def linearize_memref(ast, node_id):
	global sym_tbl;
	global tmp_stmt_lst;
	node = ast[node_id];
	# In case that there is no entry in symbol table for the current memref we create one.
	if node[1] not in sym_tbl: 
		associate_wt_new_idx(node[1]);
		lhs = ('memref', sym_tbl[node[1]], []);
		rhs = (node[0], node[1], []);
		assign = ('GETS', '', [create_new_linear_slc_node(lhs), create_new_linear_slc_node(rhs)]);
		create_new_linear_slc_assignment(assign);
	# Now it is guaranteed that there is an entry in the symbol table for the current memref.
	# To give the association up through the AST we overwrite the current AST node with the name from the symbol table.
	ast[node_id] = (node[0], sym_tbl[node[1]], node[2]);

def linearize_FOR(ast, for_node_id):
	global loop_counting_variables;
	for_node = ast[for_node_id];
	loop_init_id = for_node[2][0];
	loop_test_id = for_node[2][1];
	loop_update_id = for_node[2][2];
	seq_of_stmts_id = for_node[2][3];     seq_of_stmts = ast[seq_of_stmts_id];

	# Test whether the identifier of init, test and update are the same
	init_identifier = ast[ast[loop_init_id][2][0]][1];
	test_identifier = ast[ast[loop_test_id][2][0]][1];
	update_identifier = ast[ast[loop_update_id][2][0]][1];
	if not (init_identifier==test_identifier and init_identifier==update_identifier):
		print "\nerror: The identifier inside of a loop head is not the same for the loop: (init, test, update) = (%s, %s, %s)." % (init_identifier, test_identifier, update_identifier);
		sys.exit(1);
	init_rhs = ast[ast[loop_init_id][2][1]];
	test_rhs = ast[ast[loop_test_id][2][1]];
	if not (init_rhs[0]=='INT' and test_rhs[0]=='INT'):
		print "\nerror: The init or test right hand side of the loop header is not an integer.";
		sys.exit(1);
	lower = int(init_rhs[1]);
	upper = int(test_rhs[1]);
	loop_counting_variables.append( (for_node_id, init_identifier, lower, upper) );

def unroll_loops(ast, entry_node_id):
	collect_loop_sequences(ast, entry_node_id);
	global loop_counting_variables;
	rc=loop_counting_variables;
	while len(loop_counting_variables)>0:
		loop_seq=loop_counting_variables.pop();
		for_node_id = loop_seq[0]; for_node = ast[for_node_id];
		seq_of_stmts_id = for_node[2][3]; seq_of_stmts = ast[seq_of_stmts_id];
		counting_variable = loop_seq[1];
		lower = loop_seq[2];
		upper = loop_seq[3];
		i = lower;
		tmp_unrolled_stmt_lst = [];
		while i<upper:
			for stmt_id in seq_of_stmts[2]:
				unroll_stmt(stmt_id, counting_variable, i, tmp_unrolled_stmt_lst)
			i+=1;
		new_seq_of_stmts_id = create_new_ast_node(  ('seq_of_stmts', '', tmp_unrolled_stmt_lst)  );
		for_node_successors = for_node[2];
		for_node_successors.append(new_seq_of_stmts_id);
		ast[for_node_id] = (for_node[0], for_node[1], for_node_successors);
	return rc;

def unroll_stmt(stmt_id, counting_variable, counting_variable_value, tmp_unrolled_stmt_lst):
	stmt = ast[stmt_id];
	if stmt[0]=='GETS':
		stmt_lhs_id = stmt[2][0];
		stmt_rhs_id = stmt[2][1];
		new_lhs = ('memref', re.sub('\[%s\]' % counting_variable, '[%s]' % counting_variable_value, ast[stmt_lhs_id][1]), []);
		new_rhs = unroll_expression(stmt_rhs_id, counting_variable, counting_variable_value);
		GETS = (stmt[0], stmt[1], [create_new_ast_node(new_lhs), create_new_ast_node(new_rhs)]);
		tmp_unrolled_stmt_lst.append(  create_new_ast_node(GETS)  );
	elif stmt[0]=='FOR':
		unrolled_seq_id = stmt[2][4];
		unrolled_seq = ast[stmt[2][4]];
		for sub_stmt_id in unrolled_seq[2]:
			unroll_stmt(sub_stmt_id, counting_variable, counting_variable_value, tmp_unrolled_stmt_lst);
	else:
		print "error: During unrolling loops, found type: %s" % ast[stmt_id][0]; sys.exit(1);

def unroll_expression(stmt_rhs_id, counting_variable, counting_variable_value):
	node = ast[stmt_rhs_id];
	if node[0]=='INT' or node[0]=='FLOAT': 
		return (node[0], node[1], node[2]);
	elif node[0]=='memref':
		return ('memref', re.sub('\[%s\]' % counting_variable, '[%s]' % counting_variable_value, node[1]), []);
	elif node[0]=='expression':
		# In case of an expression, unroll all successors recursively
		expr_successors = [];
		for succ_id in node[2]:
			expr_successors.append(  unroll_expression(succ_id, counting_variable, counting_variable_value)  );
		expr_successorsids = [];
		for new_expr in expr_successors:
			expr_successorsids.append(  create_new_ast_node(new_expr)  );
		return (node[0], node[1], expr_successorsids);
	else:
		print "error: unroll_expression: unknown type %s." % node[0]; sys.exit(1);

def collect_loop_sequences(ast, node_id):
	node = ast[node_id];
	if node[0]=='FOR':
		global loop_counting_variables;
		for_node = ast[node_id];
		loop_init_id = for_node[2][0];
		loop_test_id = for_node[2][1];
		loop_update_id = for_node[2][2];
		seq_of_stmts_id = for_node[2][3];     seq_of_stmts = ast[seq_of_stmts_id];

		# Test whether the identifier of init, test and update are the same
		init_identifier = ast[ast[loop_init_id][2][0]][1];
		test_identifier = ast[ast[loop_test_id][2][0]][1];
		update_identifier = ast[ast[loop_update_id][2][0]][1];
		if not (init_identifier==test_identifier and init_identifier==update_identifier):
			print "\nerror: The identifier inside of a loop head is not the same for the loop: (init, test, update) = (%s, %s, %s)." % (init_identifier, test_identifier, update_identifier);
			sys.exit(1);
		init_rhs = ast[ast[loop_init_id][2][1]];
		test_rhs = ast[ast[loop_test_id][2][1]];
		if not (init_rhs[0]=='INT' and test_rhs[0]=='INT'):
			print "\nerror: The init or test right hand side of the loop header is not an integer.";
			sys.exit(1);
		lower = int(init_rhs[1]);
		upper = int(test_rhs[1]);
		loop_counting_variables.append( (node_id, init_identifier, lower, upper) );
		collect_loop_sequences(ast, node[2][3]);
	else:
		for succ_id in node[2]:
			collect_loop_sequences(ast, succ_id);


def ast2dot(ast):
	if slc_root not in ast: print "error: slc_root is defined wrong: %d" % slc_root; sys.exit(1);
	print "digraph {";
	ast2dot_visitor(ast, slc_root);
	print "}";


def ast2dot_visitor(ast, node_id):
	if node_id not in ast: print "error: node_id is defined wrong: %d" % node_id; sys.exit(1);
	node = ast[node_id];
	if node is None:
		print '%s [label="%s: NONE"]' % (node_id, node_id);
	else:
		if node[1]=='':
			print '%s [label="%s: %s"]' % (node_id, node_id, node[0]);
		else:
			print '%s [label="%s: %s(%s)"]' % (node_id, node_id, node[0], node[1]);
		for succ_id in node[2]:
			print "%s -> %s" % (node_id, succ_id);
		for succ_id in node[2]:
			ast2dot_visitor(ast, succ_id);


def unparse_unrolled_loops(of, ast, node_id):
	node = ast[node_id];
	if node[0]=='FOR':
		of.write("START of unrolling of loop %d ... \n" % node_id);
		unrolled_seq_of_stmts_id = node[2][4]; unrolled_seq_of_stmts = ast[unrolled_seq_of_stmts_id];
		for stmt_id in unrolled_seq_of_stmts[2]:
			assignment = ast[stmt_id];
			if assignment[0]=='GETS':
				lhs_id = assignment[2][0]; lhs = ast[lhs_id];
				rhs_id = assignment[2][1]; rhs = ast[rhs_id];
				of.write("%s=%s;\n" % (lhs[1], get_expression_string(rhs)));
			else:
				sys.exit(1);
		of.write("END of unrolling of loop %d ... \n" % node_id);
	for succ_id in node[2]:
		unparse_unrolled_loops(of, ast, succ_id);

def get_expression_string(node):
	s = '';
	if node[0]=='memref' or node[0]=='FLOAT' or node[0]=='INT':
		return node[1];
	elif node[0]=='expression':
		if node[1]=='SIN':
			s = 'sin(%s)' % (get_expression_string(ast[node[2][0]]));
		elif node[1]=='COS':
			s = 'cos(%s)' % (get_expression_string(ast[node[2][0]]));
		elif node[1]=='ADD':
			s = '%s+%s' % (get_expression_string(ast[node[2][0]]), get_expression_string(ast[node[2][1]]));
		elif node[1]=='MUL':
			s = '%s*%s' % (get_expression_string(ast[node[2][0]]), get_expression_string(ast[node[2][1]]));
		return s;
	else:
		print "unknown node type: %s" % node[0]; sys.exit(1);

####################    MAIN    ###############################
if len(sys.argv[1:])==0:
	print "Give generated ast files as paramter.";
	sys.exit(1);

for arg in sys.argv[1:]:
	if not os.path.isfile(arg): 
		print "%s is not a file." % arg;
		continue;
	# Read in AST data from file given as parameter.
	f = open(arg, 'r');
	s = '';
	for l in f.readlines():
		s+=l.replace('\n', '');
	f.close();
	ast=eval(s);
	basename , extension = os.path.splitext(arg);
	find_ast_root(f, ast);
	ast_id=slc_root+1;
	find_input_variables(ast, slc_root);
	create_linear_slc(ast);
	f = open('%s.unrolled' % basename, 'w');
	unparse_unrolled_loops(f, ast, slc_root);
	f.close();
	linearized_dot_file = "%s.linearized.dot" % basename;
	linearized_pdf_file = "%s.linearized.pdf" % basename;
	linearized_output_file = "%s.linearized" % basename;
	f = open(linearized_dot_file, 'w');
	f.write('digraph {\n');
	for key in linear_slc:
		node = linear_slc[key];
		if node[1]=='':
			f.write('%d[label="%d: %s"]\n' % (key, key, node[0]));
		else:
			f.write('%d[label="%d: %s(%s)"]\n' % (key, key, node[0], node[1]));
		for successor in node[2]:
			f.write('%d -> %d\n' % (key,successor));
	f.write('}\n');
	f.close();
	if os.stat(linearized_dot_file).st_size/1024 < 1024:
		cmd = "dot -Tpdf %s > %s" % (linearized_dot_file, linearized_pdf_file);
		os.system(cmd);
	f = open(linearized_output_file, 'w');
	unparse_linearized_slc(f);
	f.close();

sys.exit(0);
