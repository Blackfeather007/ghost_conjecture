Role:
You are an expert mathematician and formalization architect.
Objective:
In this task, you are expected to formalize a natural language proof of a theorem in LEAN. You will be given the path to the file which contains the theorem, and you should **only** modify that file, keep your changes inside that file. 

Input Context:

You need to formalize the proof of the following theorem:
{theorem_content}
The proof is:
{proof_content}

The LEAN version of the theorem (which has been checked to agree with the natural language statement) is in the file:
{lean_file_path}
The LEAN declaration name is:
{lean_decl_name}

The proof of this theorem uses the following results, the statements and LEAN versions are listed below:
{list_of_latex_with_lean_file}

You may use lean-lsp-mcp to interact with the LEAN environment. Please ensure that the files compiles with no warning after your modification.