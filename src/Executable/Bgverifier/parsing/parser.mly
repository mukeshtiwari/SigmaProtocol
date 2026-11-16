%{
  (* One start symbol per fixture file. Objects are lists of keyed members in
     any order; Ast's builders assemble them and require every field once.
     Every Base64 value is decoded and checked by Ast when it is read. *)
  open Ast
%}

%token <string> STRING
%token LBRACE RBRACE LBRACKET RBRACKET COMMA TRUE FALSE
%token DESCRIPTION CONTEXT INPUT OUTPUT STATEMENT ARGUMENT RESULT
%token P Q G PK CK H X Y Z
%token CIPHERTEXTS SHUFFLED_CIPHERTEXTS CIPHERTEXT_PRODUCT GAMMA PHIS C_A C_B B
%token CA CB PRODUCT_ARGUMENT MULTI_EXP_ARGUMENT SINGLE_VPA HADAMARD_ARGUMENT CUPPERB ZERO_ARGUMENT
%token C_D C_LOWER_DELTA C_UPPER_DELTA A_TILDE B_TILDE R_TILDE S_TILDE
%token C_A0 C_BM A R S T C_A_0 E TAU
%token EOF

%start <(Ast.shuffle_stmt * Ast.shuffle_arg) Ast.case list> shuffle_cases
%start <(Ast.product_stmt * BayerGrothlib.BayerGrothIns.product_argument) Ast.case list> product_cases
%start <(Ast.hadamard_stmt * BayerGrothlib.BayerGrothIns.hadamard_argument) Ast.case list> hadamard_cases
%start <(Ast.zero_stmt * BayerGrothlib.BayerGrothIns.zero_argument) Ast.case list> zero_cases
%start <(Ast.svp_stmt * BayerGrothlib.BayerGrothIns.svp_argument) Ast.case list> svp_cases
%start <(Ast.mexp_stmt * Ast.mexp_arg) Ast.case list> mexp_cases

%%

(* ---- the six files ---- *)

shuffle_cases: cs = cases(shuffle_stmt, shuffle_arg) { cs }
product_cases: cs = cases(product_stmt, product_arg) { cs }
hadamard_cases: cs = cases(hadamard_stmt, hadamard_arg) { cs }
zero_cases: cs = cases(zero_stmt, zero_arg) { cs }
svp_cases: cs = cases(svp_stmt, svp_arg) { cs }
mexp_cases: cs = cases(mexp_stmt, mexp_arg) { cs }

cases(stmt, arg):
  | LBRACKET cs = separated_list(COMMA, case_(stmt, arg)) RBRACKET EOF { cs }

case_(stmt, arg):
  | LBRACE ms = separated_list(COMMA, case_member(stmt, arg)) RBRACE { build_case ms }

case_member(stmt, arg):
  | DESCRIPTION d = STRING { `Description d }
  | CONTEXT c = context { `Context c }
  | INPUT i = input(stmt, arg) { `Input i }
  | OUTPUT o = output { `Output o }

input(stmt, arg):
  | LBRACE ms = separated_list(COMMA, input_member(stmt, arg)) RBRACE { build_input ms }

input_member(stmt, arg):
  | STATEMENT s = stmt { `Statement s }
  | ARGUMENT a = arg { `Argument a }

(* ---- the context and the recorded output ---- *)

context:
  | LBRACE ms = separated_list(COMMA, context_member) RBRACE { build_ctx ms }

context_member:
  | P s = STRING { `P (z_of_b64 s) }
  | Q s = STRING { `Q (z_of_b64 s) }
  | G s = STRING { `G (z_of_b64 s) }
  | PK es = elems { `Pk es }
  | CK LBRACE ms = separated_list(COMMA, ck_member) RBRACE { `Ck (build_ck ms) }

ck_member:
  | H e = elem { `H e }
  | G es = elems { `Gs es }

output:
  | b = boolean { { result = b; out_x = None; out_y = None; out_z = None } }
  | LBRACE ms = separated_list(COMMA, output_member) RBRACE { build_output ms }

output_member:
  | RESULT b = boolean { `Result b }
  | X s = STRING { `X (z_of_b64 s) }
  | Y s = STRING { `Y (z_of_b64 s) }
  | Z s = STRING { `Z (z_of_b64 s) }

boolean:
  | TRUE { true }
  | FALSE { false }

(* ---- elements, exponents, ciphertexts ---- *)

elem: s = STRING { elem_of_b64 s }
scalar: s = STRING { scalar_of_b64 s }
elems: LBRACKET es = separated_list(COMMA, elem) RBRACKET { es }
scalars: LBRACKET xs = separated_list(COMMA, scalar) RBRACKET { xs }

ciphertext:
  | LBRACE ms = separated_list(COMMA, ciphertext_member) RBRACE { build_ct ms }

ciphertext_member:
  | GAMMA e = elem { `Gamma e }
  | PHIS es = elems { `Phis es }

ciphertexts: LBRACKET cs = separated_list(COMMA, ciphertext) RBRACKET { cs }
ciphertext_rows: LBRACKET rows = separated_list(COMMA, ciphertexts) RBRACKET { rows }

(* ---- statements ---- *)

shuffle_stmt:
  | LBRACE ms = separated_list(COMMA, shuffle_stmt_member) RBRACE { build_shuffle_stmt ms }
shuffle_stmt_member:
  | CIPHERTEXTS cs = ciphertexts { `Ciphertexts cs }
  | SHUFFLED_CIPHERTEXTS cs = ciphertexts { `Shuffled cs }

product_stmt:
  | LBRACE ms = separated_list(COMMA, product_stmt_member) RBRACE { build_product_stmt ms }
product_stmt_member:
  | C_A es = elems { `Ca es }
  | B x = scalar { `B x }

hadamard_stmt:
  | LBRACE ms = separated_list(COMMA, hadamard_stmt_member) RBRACE { build_hadamard_stmt ms }
hadamard_stmt_member:
  | C_A es = elems { `Ca es }
  | C_B e = elem { `Cb e }

zero_stmt:
  | LBRACE ms = separated_list(COMMA, zero_stmt_member) RBRACE { build_zero_stmt ms }
zero_stmt_member:
  | C_A es = elems { `Ca es }
  | C_B es = elems { `Cb es }
  | Y x = scalar { `Y x }

svp_stmt:
  | LBRACE ms = separated_list(COMMA, svp_stmt_member) RBRACE { build_svp_stmt ms }
svp_stmt_member:
  | C_A e = elem { `Ca e }
  | B x = scalar { `B x }

mexp_stmt:
  | LBRACE ms = separated_list(COMMA, mexp_stmt_member) RBRACE { build_mexp_stmt ms }
mexp_stmt_member:
  | CIPHERTEXTS rows = ciphertext_rows { `Ciphertexts rows }
  | CIPHERTEXT_PRODUCT c = ciphertext { `Product c }
  | C_A es = elems { `Ca es }

(* ---- arguments ---- *)

svp_arg:
  | LBRACE ms = separated_list(COMMA, svp_member) RBRACE { build_svp ms }
svp_member:
  | C_D e = elem { `Cd e }
  | C_LOWER_DELTA e = elem { `Cdelta e }
  | C_UPPER_DELTA e = elem { `CDelta e }
  | A_TILDE xs = scalars { `Atilde xs }
  | B_TILDE xs = scalars { `Btilde xs }
  | R_TILDE x = scalar { `Rtilde x }
  | S_TILDE x = scalar { `Stilde x }

zero_arg:
  | LBRACE ms = separated_list(COMMA, zero_member) RBRACE { build_zero ms }
zero_member:
  | C_A0 e = elem { `Ca0 e }
  | C_BM e = elem { `Cbm e }
  | C_D es = elems { `Cds es }
  | A xs = scalars { `A xs }
  | B xs = scalars { `B xs }
  | R x = scalar { `R x }
  | S x = scalar { `S x }
  | T x = scalar { `T x }

hadamard_arg:
  | LBRACE ms = separated_list(COMMA, hadamard_member) RBRACE { build_hadamard ms }
hadamard_member:
  | CUPPERB es = elems { `CB es }
  | ZERO_ARGUMENT z = zero_arg { `Zero z }

mexp_arg:
  | LBRACE ms = separated_list(COMMA, mexp_member) RBRACE { build_mexp ms }
mexp_member:
  | C_A_0 e = elem { `Ca0 e }
  | C_B es = elems { `Cbs es }
  | E cs = ciphertexts { `E cs }
  | A xs = scalars { `A xs }
  | R x = scalar { `R x }
  | B x = scalar { `B x }
  | S x = scalar { `S x }
  | TAU x = scalar { `Tau x }

product_arg:
  | LBRACE ms = separated_list(COMMA, product_member) RBRACE { build_product ms }
product_member:
  | C_B e = elem { `Cb e }
  | HADAMARD_ARGUMENT h = hadamard_arg { `Hadamard h }
  | SINGLE_VPA s = svp_arg { `Svp s }

shuffle_arg:
  | LBRACE ms = separated_list(COMMA, shuffle_member) RBRACE { build_shuffle ms }
shuffle_member:
  | CA es = elems { `Ca es }
  | CB es = elems { `Cb es }
  | PRODUCT_ARGUMENT pa = product_arg { `Product pa }
  | MULTI_EXP_ARGUMENT me = mexp_arg { `Mexp me }
