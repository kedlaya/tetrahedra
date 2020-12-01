This repository consists of code and data associated to the paper "Space vectors forming rational angles" by Kiran S. Kedlaya, Alexander Kolpakov, Bjorn Poonen, and Michael Rubinstein ([arXiv:2011.14232](https://arxiv.org/abs/2011.14232)).

The code uses a combination of platforms: C++, [SageMath](https://www.sagemath.org/) version 9.2, and [Magma](magma.maths.usyd.edu.au/) version 2.25-6. (SageMath also uses [Singular](https://www.singular.uni-kl.de/) as an embedded component.) The C++ code depends on [Bailey's quad double library QD](https://www.davidhbailey.com/dhbsoftware/) version 2.3.22 for floating-point computations in quad-double precision.
Some of the SageMath code is embedded in [Jupyter](https://jupyter.org/) notebooks; these were originally run on [CoCalc](https://cocalc.com).

- `Numerical computations/`:

  - `README.md`: C++ compilation notes.
  - `low_order_solutions.cc`: C++ code to enumerate configurations of 4 lines whose angles are multiples of $\pi/N$ for a fixed value of $N$ (Section 8, Proposition 8.1). The rigorous analysis of the paper shows that this code produces no false negatives.
  - `DATA/`: output of the C++ code.
  - `algebraic_verification.ipynb`: Jupyter/SageMath notebook to rule out false positives in the C++ output using algebraic computations (Section 8, Proposition 8.1).
  - `group-sporadics.ipynb`: Jupyter/SageMath notebook to generate the table of sporadic tetrahedra from the output of the C++ code (Section 11, Table 3).

- `Algebraic computations/`: 

  - `torsion_closure.sage`: SageMath code to compute torsion closures of general ideals in Laurent polynomial rings (Section 7; see also below).
  - `tetrahedra_degenerate.ipynb`: Jupyter/SageMath notebook to compute solutions of the Gram determinant equation corresponding to degenerate tetrahedra (Section 9, Lemma 9.3).
  - `tetrahedra.ipynb`: Jupyter/SageMath notebook to compute solutions of the Gram determinant equation corresponding to nondegenerate tetrahedra (Section 9, Lemma 9.5). This depends on `torsion_closure.sage`.

- `Conversion to angles/`: 

  - `4-vector-configurations-1-parameter-families.ipynb`, `4-vector-configurations-2-parameter-families.ipynb`: Jupyter/SageMath notebooks to convert parametric solutions of the Gram determinant equation into families of rational-angle line configurations (Section 1, Theorem 1.2, as well as Section 9, Lemma 9.3 and Lemma 9.5).
  - `4-vector-configurations-tetrahedra.ipynb`: Jupyter/SageMath notebook to run consistency checks on the output stored in the `DATA/` folder and to interpret it in human-readable format (Section 1, Theorem 1.8, as well as Section 9, Lemma 9.6).

- `Larger configurations/`:

    - `tetrahedra.m`, `tetrahedra-compute.m`: Magma code to assemble rational-angle line configurations with more than 4 lines (Section 10), and to generate the tables of these (Section 11).
    - `Maximal_Configurations.txt`: output of the previous code.
    - `all-2.24-5.save`, `all-2.25-6`: Magma saved workspaces with the tables generated (for the indicated versions of Magma).


