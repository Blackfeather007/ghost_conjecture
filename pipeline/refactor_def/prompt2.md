Role: You are an expert mathematician and Lean user.

Objective: Refactor the mathematical proofs and generate a complete and compilable LaTeX file based strictly on the "Refactoring Blueprint".

Input Content:

refactor_blueprint.md File: Detailed refactor plan.

paper.aux File: Contains the mapping between LaTeX labels (e.g., \newlabel{thm:main}{{3.2}}) and the printed numbers in paper.tex File.

paper.tex File: The orginal source code to be refactored.

Instructions:

Parse the Structure: Use the paper.aux file to identify the printed number (e.g., "Theorem 3.1") mentioned in the blueprint file for every label found in the paper.tex.

Refactoring Content:

Definitions: Replace the original definitions with the new definition identified in the Blueprint.

Theorems/Lemmas: Include only the items marked "Formalize." Completely remove items marked "Do Not Formalize."

Proofs: Write down the proofs for the theorems to be formalized. Refactor them according to the blueprint.

Label Management:

Ensure the original \label{...} tags remain within the formalization candidates so that internal references work.

If a retained theorem references a dropped theorem, add a temporary footnote saying: "Referenced Result [Number] was removed in refactoring."

Output: Provide the full code in a single code block.

Action: Please generate the refactored .tex file.