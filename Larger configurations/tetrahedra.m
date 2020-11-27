/* In Magma, type    
      load "tetrahedra.m";
   to load these routines; this may take a minute. 

   Or, type
      restore "all.save";
   to restore a Magma workspace in which the major procedures at the bottom have already been run, if you want to see the results without having to wait hours.

   Suggestion for understanding this file: Read the comments in the CONVERSIONS section to learn the different formats being used, and then go to the bottom of the file to see the top-level routines. */

/* ----------------------------------------------------------------------- */
/* INITIALIZATION */

/* Use the Magma profiler to see how much time is being used by the various subroutines, after a computation has been done. */

SetProfile(true);
ProfileReset();

/* Initialize Z, Q, R, and pi. Set up a polynomial ring Q[t,u,v] whose variables will be used as parameters. */

ZZ:=Integers();
QQ:=Rationals();
QQpoly<t,u,v>:=PolynomialRing(QQ,3);
precision:=20;
RR:=RealField(precision);
pi:=Pi(RR);

/* maxsize is the maximum n such that an n x n AngleMatrix will be examined.  The icosidodecahedron configuration contains 15 vectors, up to sign; to make sure that it does not extend, we need to examine 16-vector configurations. */
maxsize:=16;

/* ----------------------------------------------------------------------- */
/* INTEGER ROUTINES */

/* nFromN(N) returns the positive integer n such that 1 + n(n-1)/2 = N.  (Below, an n x n angle matrix corresponds to an N-long ATV.) */

function nFromN(N)
   discard,sqrt := IsSquare(8*N-7);
   return ExactQuotient(sqrt+1,2);
end function;

/* ----------------------------------------------------------------------- */
/* RATIONAL NUMBER ROUTINES */

/* MaxDenominator(seq) takes a vector of rational numbers and returns the largest denominator. */

function MaxDenominator(vec)
   return Max([Denominator(q):q in Eltseq(vec)]);
end function;

/* DenominatorSum(seq) takes a vector of rational numbers and returns the sum of their denominators. */

function DenominatorSum(vec)
   return &+ [Denominator(q):q in Eltseq(vec)];
end function;

/* LCD(seq) takes a sequence of rational numbers and returns their least common denominator. */

function LCD(seq)
   return LCM([Denominator(q):q in seq]);
end function;

/* RationalGCD(seq) takes a sequence of rational numbers and returns the nonnegative generator of the additive subgroup of Q they generate. */

function RationalGCD(seq)
   n:=LCD(seq);
   intseq:=[ZZ!(n*q) : q in seq];
   return GCD(intseq)/n;
end function;

/* ----------------------------------------------------------------------- */
/* SUBSETS */

/* subset3(m) is the sequence of 3-element subsets of {1,2,..m} in some order.  The ordering is partially specified, in order to improve running time of the merging algorithms. */

function subsets3(m)
   firstsets := [ {a,a+1,a+2} : a in [1..m-2] ];
   secondsets := SetToSequence( Subsets({1..m},3) diff SequenceToSet(firstsets) );
   return firstsets cat secondsets;
end function;

function subsets3old(m)
   return Sort(SetToSequence(Subsets({1..m},3)),func<x,y | Max(x)-Max(y) >);
end function;

/* Subsets4[n] is a sequence of 4-element subsets of {1,...,n} containing n, in increasing order of second largest element.  The ordering is important for the running time of the major algorithms. */

Subsets4 := [ [set3 join {n} : set3 in subsets3(n-1)] : n in [1..maxsize] ];

/* ----------------------------------------------------------------------- */
/* ELEMENTARY SEQUENCE, VECTOR, AND MATRIX ROUTINES */


/* EliminateDuplicates(seq) takes a sequence seq, removes duplicates, and returns the possibly shorter resulting sequence. */

function EliminateDuplicates(seq)
   return SetToSequence(SequenceToSet(seq));
end function;

/* SequenceDiff(seq1,seq2) returns a sequence of elements that are in seq1 but not in seq2, without multiplicity. */

function SequenceDiff(seq1,seq2)
   return SetToSequence(SequenceToSet(seq1) diff SequenceToSet(seq2));
end function;

/* ElementFrequency(seq,elt) returns the number of appearances of elt in the sequence seq. */

function ElementFrequency(seq,elt)
   return #[1 : e in seq | e eq elt];
end function;

/* Q6(a,b,c,d,e,f) takes six rational numbers, and returns (a,b,c,d,e,f) as a vector in Q^6. */

function Q6(a,b,c,d,e,f)
   return Vector(QQ,[a,b,c,d,e,f]);
end function;

/* CompareSequences(seq1,seq2) takes two sequences of rational numbers having the same length, and return -1, 0, 1 according to whether seq1 is lexicographically earlier, seq1 = seq2, or seq1 is lexicographically later. */

function CompareSequences(seq1,seq2)
   v1:=Vector(seq1);
   v2:=Vector(seq2);
   if v1 lt v2
      then return -1;
   elif v1 gt v2
      then return 1;
   else return 0;
   end if;
end function;

/* RoundSequence(seq) takes a sequence of rational numbers, and rounds each to the nearest integer. */

/* RoundVector(vec) is the same, but for a vector with rational coordinates. */

function RoundSequence(seq)
   return [Round(q): q in seq];
end function;

function RoundVector(vec)
   return Vector(QQ,RoundSequence(Eltseq(vec)));
end function;


/* StandardBasisElement(N,j) returns the j-th standard basis vector of Q^N */

function StandardBasisElement(N,j)
   return CharacteristicVector(VectorSpace(QQ,N),{j});
end function;

/* CosineOfAngleBetween(v,w) takes two rational or real vectors v and w, and returns the cosine of the angle between them, as a real number in [-1,1]. */
function CosineOfAngleBetween(v,w)
   return DotProduct(v,w) / Sqrt(Norm(v) * Norm(w));
end function;

/* AugmentVector(a,vec) takes a vector vec in Q^n, and prepends a to obtain a vector in Q^{n+1}. */

function AugmentVector(a,vec)
  return Vector(QQ,[a] cat Eltseq(vec));
end function;

/* DiminishVector(vec) take a vector vec in Q^n, and removes its first coordinate to get a vector in Q^{n-1}. */

function DiminishVector(vec)
  return Vector(QQ,Remove(Eltseq(vec),1));
end function;

/* AugmentMatrix(a,mat) takes a rational number a and a matrix mat, and returns the block diagonal matrix with a 1 x 1 block containing a in the upper left, and with mat as a block in the lower right. */

function AugmentMatrix(a,mat)
  return DiagonalJoin(Matrix(QQ,1,1,[a]),mat);
end function;

/* MinorMatrix(mat,I) takes an n x n matrix mat and a subset I of {1,...,n}, and returns the square submatrix whose rows and columns are indexed by I. */

function MinorMatrix(mat,I)
  J:=Sort(SetToSequence(I));
  m:=#J;
  return Matrix(BaseRing(mat),m,m,[[mat[i,j] : j in J] : i in J]);
end function;

/* ----------------------------------------------------------------------- */
/* SUBSPACE ROUTINES */

/* EchelonMatrix(W) takes a subspace W of Q^n, and returns a matrix in reduced row echelon form whose rows are a basis of W. */

function EchelonMatrix(W)
   return EchelonForm(BasisMatrix(W));
end function;

/* InverseImageSubspace(f,W) takes a linear transformation (matrix) f: U --> V and a subspace W of V, and returns f^{-1} W as a subspace of U. */

function InverseImageSubspace(f,W)
  V:=Generic(W);
  quotient, q:= V/W;
  qmat:=KMatrixSpace(QQ,Dimension(V),Dimension(quotient))!q;
  return Kernel(f*qmat);
end function;

/* Subsetneq(sub1,sub2) takes two subspaces and returns True if sub1 is strictly contained in sub2. */

function Subsetneq(sub1,sub2)
   return sub1 subset sub2 and sub1 ne sub2;
end function;

/* EliminateSubsubspaces(seq) takes a sequence of subspaces, and returns the sequence of those that are not strictly contained in another. */

function EliminateSubsubspaces(seq);
   return [ sub1 : sub1 in seq | not &or [Subsetneq(sub1,sub2):sub2 in seq] ];
end function;

/* nOfSubspace(sub) takes a subspace parametrizing ATVs corresponding to n x n AngleMatrices, and returns n. */

function nOfSubspace(sub)
   return nFromN(Degree(sub));
end function;

/* ----------------------------------------------------------------------- */
/* CONVERSIONS */

/* Angles are represented by rational numbers: e.g., 1/3 means pi/3. */

/* RubinsteinToDihedral6(rub) takes a tuple rub =  <n, seq>, where n is a positive integer and seq is a sequence of integers, and returns the vector (1/n)seq with rational coordinates.  The output is interpreted as the vector (a12, a34, a13, a24, a14, a23), where aij is the dihedral angle between faces i and j of a tetrahedron.  */

/* Dihedral6ToRubinstein(dih) is the inverse operation, recovering n as the LCM of the denominators of the coordinates. */

function RubinsteinToDihedral6(rub);
  n:=rub[1];
  ints:=rub[2];
  return Vector(6,[(QQ!ints[i])/n : i in [1..6]]);
end function;

function Dihedral6ToRubinstein(dih);
  n:=LCD(Eltseq(dih));
  ints:=[ZZ!(n*dih[i]) : i in [1..6]];
  return < n,ints >;
end function;

/* Dihedral6ToAngle6(dih) converts the vector of dihedral angles to the vector of angles between pairs of outward normals; this amounts to replacing each angle a by pi-a. */

/* Angle6ToDihedral6(angle6) is the inverse operation (which is the same!) */

function Dihedral6ToAngle6(dih)
  return Vector(6,[1-dih[i]:i in [1..6]]);
end function;

function Angle6ToDihedral6(angle6)
  return Vector(6,[1-angle6[i]:i in [1..6]]);
end function;

/* Angle6ToTV(angle6) maps (a12, a34, a13, a24, a14, a23) to (a12, a13, a14, a23, a24, a34).  (TV is an abbreviation for Triangular Vector; its coordinates will later be placed in the upper triangle of a matrix.) */

/* TVToAngle6(tv) is the inverse operation. */

function Angle6ToTV(angle6)
  return Vector(6,[angle6[1],angle6[3],angle6[5],angle6[6],angle6[4],angle6[2]]);
end function;

function TVToAngle6(tv)
  return Vector(6,[tv[1],tv[6],tv[2],tv[5],tv[3],tv[4]]);
end function;

/* TVToAngleMatrix(vec), where vec is a vector of length n(n-1)/2 returns an n x n symmetric matrix with zeros along the diagonal and whose entries above the diagonal are given by vec, from left to right, then top to bottom */

/* AngleMatrixToTV(mat) is the inverse operation. */

function TVToAngleMatrix(vec)
  almostmatrix:=UpperTriangularMatrix(Eltseq(vec));
  n:=Ncols(almostmatrix)+1;
  U:=VerticalJoin(
        HorizontalJoin(ZeroMatrix(QQ,n-1,1),
                       almostmatrix
                       ),
        ZeroMatrix(QQ,1,n)
      );
  return U+Transpose(U);
end function;

function AngleMatrixToTV(mat)
  n:=Ncols(mat);
  seq:=[];
  for i in [1..n-1] do
     seq cat:= [ mat[i,j] : j in [i+1..n] ];
  end for;
  return Vector(QQ,seq);
end function;

/* VectorConfigurationToCosineMatrix(seq), where seq is a sequence of vectors in R^3 (although it would work in R^m as well), returns the CosineMatrix containing the cosines of the angles between them. */

function VectorConfigurationToCosineMatrix(seq)
   n:=#seq;
   return Matrix(RR,n,n,[CosineOfAngleBetween(seq[i],seq[j]) : i in [1..n], j in [1..n]]);
end function;

/* RationalToCosine(r) takes a rational number r and returns the real number Cos(r*pi). */

/* CosineToRational(c) takes a real number c and tries to find a rational number r of denominator <= 1000 such that Cos(r*pi) = c.  If no such r exists, an error results. */

function RationalToCosine(r)
  return Cos(pi*r);
end function;

function CosineToRational(c)
  assert AbsoluteValue(c) le 1;
  x:=Arccos(c)/pi;
  r:=BestApproximation(x,1000);
  assert AbsoluteValue(r-x) le 10^(5-precision);
  return r;
end function;

/* AngleMatrixToCosineMatrix(mat) takes a matrix of angles, and applies RationalToCosine entrywise. */

/* CosineMatrixToAngleMatrix(mat) is the inverse operation. */

function AngleMatrixToCosineMatrix(mat)
  m:=NumberOfRows(mat);
  n:=NumberOfColumns(mat);
  return Matrix(RR,m,n,[RationalToCosine(mat[i,j]) : i in [1..m], j in [1..n]]);
end function;

function CosineMatrixToAngleMatrix(mat)
  m:=NumberOfRows(mat);
  n:=NumberOfColumns(mat);
  return Matrix(QQ,m,n,[CosineToRational(mat[i,j]) : i in [1..m], j in [1..n]]);
end function;

/* AngleMatrixToCosineDet(mat) takes the determinant of AngleMatrixToCosineMatrix(mat). */

function AngleMatrixToCosineDet(mat)
  return Determinant(AngleMatrixToCosineMatrix(mat));
end function;

/* Dihedral6FamilyToAngle6Family(seq) takes a sequence [a_1,a_2,...,a_r] of Dihedral6 vectors, interprets it as the family a_1 + a_2*t_2 + ... + a_r*t_r depending on rational parameters t_2,...,t_r, applies Dihedral6ToAngle6 to send each angle to 1-itself, and then retrieves the coefficient vectors again.  Explicitly, each coordinate of the first vector is sent to 1-itself, and each subsequent vector is negated. */

function Dihedral6FamilyToAngle6Family(seq)
   return [Dihedral6ToAngle6(seq[1])] cat [-seq[i] : i in [2..#seq]];
end function;

/* Angle6FamilyToTVFamily(seq) takes a sequence [a_1,a_2,...,a_r] of angle6 vectors, and returns the sequence of corresponding TV vectors. */

function Angle6FamilyToTVFamily(seq)
   return [Angle6ToTV(angle6) : angle6 in seq];
end function;

/* TVFamilyToSubspace(seq) takes a sequence [a_1,a_2,...,a_r] of TV vectors, interprets it as the family a_1 + a_2*t_2 + ... + a_r*t_r depending on rational parameters t_2,...,t_r, and returns the subspace spanned by the corresponding ATVs. */

/* TVToSubspace(tv) is the same, but takes just one TV, and returns a 1-dimensional subspace. */

function TVFamilyToSubspace(seq)
   v1:=AugmentVector(1,seq[1]);
   space:=sub< Parent(v1) | v1, [AugmentVector(0,seq[i]) : i in [2..#seq]] >;
   return space;
end function;

function TVToSubspace(tv)
   return TVFamilyToSubspace([tv]);
end function;

/* AngleMatrixFamilyToTVFamily(seq) takes a sequence [a_1,a_2,...,a_r] of AngleMatrices, and returns the sequence of corresponding TV vectors. */

function AngleMatrixFamilyToTVFamily(seq)
   return [AngleMatrixToTV(am) : am in seq];
end function;

/* SubspaceToTVFamily(sub) takes a subspace sub of ATVs, finds the echelonized basis, drops the first 1 or 0 of each ATV, and returns the sequence of resulting TVs. */

function SubspaceToTVFamily(sub)
   mat:=EchelonMatrix(sub);
   if IsZero(Transpose(mat)[1]) then return [];
      else return [DiminishVector(mat[i]): i in [1..Nrows(mat)]];
   end if;
end function;

/* VectorFamilyToParametrizedVector(seq) takes a sequence of vectors and returns seq[1] + t * seq[2] + u * seq[3] + ... */

function VectorFamilyToParametrizedVector(seq)
   constantterm:=seq[1];
   universe:=Parent(t*constantterm);
   return seq[1] + &+ [universe | QQpoly.i * seq[i+1] : i in [1..#seq-1]];
end function;

/* MatrixFamilyToParametrizedMatrix(seq) takes a sequence of matrices and returns seq[1] + t * seq[2] + u * seq[3] + ... */

function MatrixFamilyToParametrizedMatrix(seq)
   constantterm:=seq[1];
   universe:=Parent(t*constantterm);
   return seq[1] + &+ [universe | QQpoly.i * seq[i+1] : i in [1..#seq-1]];
end function;

/* ----------------------------------------------------------------------- */
/* COMPOSITIONS */

function RubinsteinToAngle6(rub)
  return Dihedral6ToAngle6(RubinsteinToDihedral6(rub));
end function;

function RubinsteinToTV(rub)
  return Angle6ToTV(RubinsteinToAngle6(rub));
end function;

function RubinsteinToATV(rub)
  return AugmentVector(1,RubinsteinToTV(rub));
end function;

function RubinsteinToAngleMatrix(rub)
  return TVToAngleMatrix(RubinsteinToTV(rub));
end function;

function RubinsteinToCosineDet(rub)
  return AngleMatrixToCosineDet(RubinsteinToAngleMatrix(rub));
end function;

function RubinsteinToSubspace(rub)
   return TVToSubspace(RubinsteinToTV(rub));
end function;

/* --- */

function Dihedral6ToTV(dih)
  return Angle6ToTV(Dihedral6ToAngle6(dih));
end function;

function Dihedral6ToAngleMatrix(dih)
  return TVToAngleMatrix(Dihedral6ToTV(dih));
end function;

function Dihedral6ToCosineDet(dih)
  return AngleMatrixToCosineDet(Dihedral6ToAngleMatrix(dih));
end function;

function Dihedral6ToSubspace(dih)
   return TVToSubspace(Dihedral6ToTV(dih));
end function;

/* --- */

function Angle6ToRubinstein(angle6)
   return Dihedral6ToRubinstein(Angle6ToDihedral6(angle6));
end function;

function Angle6ToAngleMatrix(angle6)
  return TVToAngleMatrix(Angle6ToTV(angle6));
end function;

function Angle6ToCosineDet(angle6)
  return AngleMatrixToCosineDet(Angle6ToAngleMatrix(angle6));
end function;

function Angle6ToSubspace(angle6)
   return TVToSubspace(Angle6ToTV(angle6));
end function;

/* --- */

function TVToRubinstein(tv)
   return Angle6ToRubinstein(TVToAngle6(tv));
end function;

function TVToDihedral6(tv)
   return Angle6ToDihedral6(TVToAngle6(tv));
end function;

function TVToCosineDet(tv)
  return AngleMatrixToCosineDet(TVToAngleMatrix(tv));
end function;

/* --- */

function ATVToRubinstein(atv)
   return TVToRubinstein(DiminishVector(atv));
end function;

function ATVToAngleMatrix(atv)
   return TVToAngleMatrix(DiminishVector(atv));
end function;

function ATVToCosineDet(atv)
  return TVToCosineDet(DiminishVector(atv));
end function;

function ATVToSubspace(atv)
   return TVToSubspace(DiminishVector(atv));
end function;

/* --- */

function AngleMatrixToSubspace(mat)
   return TVToSubspace(AngleMatrixToTV(mat));
end function;

function AngleMatrixToAngle6(mat)
   return TVToAngle6(AngleMatrixToTV(mat));
end function;

function AngleMatrixToDihedral6(mat)
   return TVToDihedral6(AngleMatrixToTV(mat));
end function;

function AngleMatrixToRubinstein(mat)
   return TVToRubinstein(AngleMatrixToTV(mat));
end function;

/* --- */

function VectorConfigurationToAngleMatrix(seq)
   return CosineMatrixToAngleMatrix(VectorConfigurationToCosineMatrix(seq));
end function;

function VectorConfigurationToSubspace(seq)
   return AngleMatrixToSubspace(VectorConfigurationToAngleMatrix(seq));
end function;

/* --- */

function Angle6FamilyToDihedral6Family(seq)
   return Dihedral6FamilyToAngle6Family(seq);
end function;

function Angle6FamilyToSubspace(seq)
   return TVFamilyToSubspace(Angle6FamilyToTVFamily(seq));
end function;

/* --- */

function TVFamilyToAngleMatrixFamily(seq)
   return [TVToAngleMatrix(tv) : tv in seq];
end function;

function TVFamilyToAngle6Family(seq)
   return [TVToAngle6(tv) : tv in seq];
end function;

function TVFamilyToDihedral6Family(seq)
   return Angle6FamilyToDihedral6Family(TVFamilyToAngle6Family(seq));
end function;

/* --- */

function Dihedral6FamilyToTVFamily(seq)
   return Angle6FamilyToTVFamily(Dihedral6FamilyToAngle6Family(seq));
end function;

function Dihedral6FamilyToAngleMatrixFamily(seq)
   return TVFamilyToAngleMatrixFamily(Dihedral6FamilyToTVFamily(seq));
end function;

function Dihedral6FamilyToSubspace(seq)
   return TVFamilyToSubspace(Dihedral6FamilyToTVFamily(seq));
end function;

/* --- */

function AngleMatrixFamilyToDihedral6Family(seq)
   return [AngleMatrixToDihedral6(mat) : mat in seq];
end function;

function AngleMatrixFamilyToAngle6Family(seq)
   return [AngleMatrixToAngle6(mat) : mat in seq];
end function;

function AngleMatrixFamilyToSubspace(seq)
   return TVFamilyToSubspace(AngleMatrixFamilyToTVFamily(seq));
end function;

/* --- */

function SubspaceToAngleMatrixFamily(sub)
  return TVFamilyToAngleMatrixFamily(SubspaceToTVFamily(sub));
end function;

function SubspaceToAngle6Family(sub)
  return TVFamilyToAngle6Family(SubspaceToTVFamily(sub));
end function;

function SubspaceToDihedral6Family(sub)
  return TVFamilyToDihedral6Family(SubspaceToTVFamily(sub));
end function;

/* SubspaceToTV(sub) checks that dim(sub)=1, and if so, returns the corresponding single TV. */

function SubspaceToTV(sub)
  assert Dimension(sub) eq 1;
  return SubspaceToTVFamily(sub)[1];
end function;

function SubspaceToAngleMatrix(sub)
   return TVToAngleMatrix(SubspaceToTV(sub));
end function;

function SubspaceToAngle6(sub)
   return TVToAngle6(SubspaceToTV(sub));
end function;

function SubspaceToDihedral6(sub)
   return TVToDihedral6(SubspaceToTV(sub));
end function;

function SubspaceToRubinstein(sub)
   return TVToRubinstein(SubspaceToTV(sub));
end function;

function SubspaceToParametrizedMatrix(sub)
   return MatrixFamilyToParametrizedMatrix(SubspaceToAngleMatrixFamily(sub));
end function;

/* ----------------------------------------------------------------------- */

/* IsApproximatelyZero(x) returns True if x is 0 to within a certain numerical error. */

function IsApproximatelyZero(x)
   return AbsoluteValue(x) lt 10^(5-precision);
end function;

/* TestSubspace(sub) returns True if a particular combination of the TVs in sub, when converted to a 4 x 4 matrix of cosines, satisfies the zero determinant condition.  (There is a chance of false positives.) */

testcombination:=[1,1/17,1/19,1/23];

function TestSubspace(sub)
   d:=Dimension(sub);
   testATV:=Vector(QQ,testcombination[1..d])*EchelonMatrix(sub);
   det:=ATVToCosineDet(testATV);
   return IsApproximatelyZero(det);
end function;

/* TestSubspaces(seq) takes a sequence of subspaces, and returns True if TestSubspace returns True for all of them. */

function TestSubspaces(seq)
   return &and [TestSubspace(sub) : sub in seq];
end function;

/* SpecializeSubspace(sub,parameters) takes a subspace sub corresponding to an r-parameter family and a vector "parameters" in Q^r, and returns the subspace corresponding to the 0-parameter family obtained by specializing the parameters to "parameters". */

function SpecializeSubspace(sub,parameters)
   testATV:=AugmentVector(1,parameters)*EchelonMatrix(sub);
   return ATVToSubspace(testATV);
end function;

/* Specialization(sub) returns a sample 1-dimensional subspace of sub. */

function Specialization(sub)
   r := Dimension(sub);
   parameters := Vector(QQ,testcombination[2..r]);
   return SpecializeSubspace(sub,parameters);
end function;


/* ----------------------------------------------------------------------- */

/* AngleMatrix3Inequalities(mat,one) takes a 3 x 3 angle matrix (symmetric, with 0s along the diagonal) and a rational number "one", and returns a sequence of the four quantities that must be nonnegative for the matrix to come from a 4-tuple of vectors in R^3, assuming that "one" is 1.   The "one" argument is there so that the function can be applied in cases when the entries of mat are coefficients of a parameter, in which case "one" should be set to 0. */

function AngleMatrix3Inequalities(mat, one)
   a:=mat[1,2];
   b:=mat[1,3];
   c:=mat[2,3];
   return [a+b-c, b+c-a, c+a-b, 2*one-a-b-c];
end function;

/* AngleMatrixInequalities(mat,one) takes an n x n angle matrix (symmetric, with 0s along the diagonal) and a rational number "one", and returns a sequence of the quantities whose nonnegativity is necessary (but not sufficient) for the matrix to come from a n-tuple of vectors in R^3.  The argument "one" is as in AngleMatrix3Inequalities. */

function AngleMatrixInequalities(mat,one)
   n:=Nrows(mat);
   return &cat [ AngleMatrix3Inequalities(MinorMatrix(mat,I),one) : I in Subsets({1..n},3) ];
end function;

function Dihedral6Inequalities(dih,one)
   return AngleMatrixInequalities(Dihedral6ToAngleMatrix(dih),one);
end function;

function Angle6Inequalities(angle6,one)
   return AngleMatrixInequalities(Angle6ToAngleMatrix(angle6),one);
end function;

function TVInequalities(angle6,one)
   return AngleMatrixInequalities(TVToAngleMatrix(angle6),one);
end function;

function ATVInequalities(atv)
   return TVInequalities(DiminishVector(atv),atv[1]);
end function;

function TVFamilyInequalities(tvfamily)
   return [TVInequalities(tvfamily[1],1)] cat [TVInequalities(tvfamily[i],0) : i in [2..#tvfamily]];
end function;

/* IsPlanarAngleMatrixFamily(seq) takes a realizable AngleMatrixFamily and returns True if it corresponds to a configuration of vectors in a plane.  It assumes that each pair of vectors is independent. */
/* IsPlanarAngleMatrix3Family(seq) is the same in the 3 x 3 case. */

function IsPlanarAngleMatrix3Family(seq) 
  mat := Matrix(QQ,[ AngleMatrix3Inequalities(seq[1], 1) ] cat [ AngleMatrix3Inequalities(seq[i], 0) : i in [2..#seq]]);
  trans := Transpose(mat);
  assert Nrows(trans) eq 4;
  return &or [IsZero(trans[i]): i in [1..4]];
end function;

function IsPlanarAngleMatrixFamily(seq) 
   n:=Nrows(seq[1]);
   for i in [3..n] do
      if not IsPlanarAngleMatrix3Family([MinorMatrix(mat,{1,2,i}) : mat in seq]) 
          then return false;
      end if;
   end for;
   return true;
end function;

/* IsPerpAngleMatrixFamily(seq) returns True if some row has all entries of the ParametrizedMatrix equal to 1/2 except the entry on the diagonal. */

function IsPerpAngleMatrixFamily(seq)
   n:=Nrows(seq[1]);
   return &or [ &and Remove([(seq[1][i,j] eq 1/2) and (&and [seq[k][i,j] eq 0 : k in [2..#seq]]) : j in [1..n]],i) : i in [1..n]];
end function;

/* ----------------------------------------------------------------------- */

/* Angle6FamilyRange(seq) takes an Angle6Family seq corresponding to a 1-parameter family, and returns the range of values for the parameter for which the six angles satisfy the 12 inequalities necessary for it to come from a 4-tuple of vectors in R^3.  The range is returned as a sequence [a,b] with a <= b.  If the range is empty, then an empty sequence [] is returned. */

/* Dihedral6FamilyRange(seq) does the same for a Dihedral6Family. */

function Angle6FamilyRange(seq)
   assert #seq eq 2;
   lowerbounds:=[QQ|];
   upperbounds:=[QQ|];
   inequalitiesconstants := Angle6Inequalities(seq[1],1);
   inequalitieslinears := Angle6Inequalities(seq[2],0);
   for i in [1..#inequalitiesconstants] do
      a := inequalitieslinears[i];
      b := inequalitiesconstants[i];
      if a eq 0 then 
         if b lt 0 then return []; end if;
      elif a gt 0 then
         Append(~lowerbounds,-b/a);
      else
         Append(~upperbounds,-b/a);
      end if;
   end for;
   lower := Max(lowerbounds);
   upper := Min(upperbounds);
   if lower gt upper then
      return [];
   else return [lower,upper];
   end if;
end function;

function Dihedral6FamilyRange(seq)
   return Angle6FamilyRange(Dihedral6FamilyToAngle6Family(seq));
end function;

/* AdjustDihedral6Range(seq) takes a 1-parameter Dihedral6Family and returns the same family with the parameter shifted so that the parameter range is [0,a] for some a. */

function AdjustDihedral6Range(seq)
   oldrange:=Dihedral6FamilyRange(seq);
   return [seq[1]+oldrange[1]*seq[2],seq[2]];
end function;

/* FixKedlayaDihedral6Family(seq) takes a length-2 sequence of Dihedral6 vectors representing a 1-parameter family of Dihedral6 vectors (the first vector contains the constant terms, and the second vector is the vector of coefficients of the parameter), and returns a sequence each term of which is itself a length-2 sequence of Dihedral6 vectors, but now adjusted so that the parametrized family takes value in [0,1]^6 for some value of the parameter, and discard results for which any of the 12 inequalities fail.  It does this by shifting coordinates by elements of 2Z and changing their sign, differently for different ranges of the parameter.   Finally, it shifts the parameter of each family so that the parameter range is [0,a] for some rational number a. */

function FixKedlayaDihedral6Family(seq)
   assert #seq eq 2;
   output:=[Parent(seq)|];  /* Initialize output to be an empty sequence whose elements will be of the same type as seq. */
   constantcoefficients:=seq[1];
   linearcoefficients:=seq[2];
   q:=RationalGCD(Eltseq(linearcoefficients));
   max:=2/q;        /* The relevant range for the parameter is [0,max]. */
   transitionpoints:=[0,max];
   for i in [1..6] do 
      a:=linearcoefficients[i];
      b:=constantcoefficients[i]; 
          /* The i-th coordinate in the input parametrized family is at+b. */
      if a ne 0 then 
         outputrange := [ a*0 + b , a*max + b ]; 
                    /* These will be in reverse order if a<0. */
         for j in [Ceiling(Min(outputrange))..Floor(Max(outputrange))] do
            Append(~transitionpoints,(j-b)/a);
         end for;
      end if;
   end for;
   transitionpoints:=Sort(EliminateDuplicates(transitionpoints));
           /* transitionpoints is the sequence of rational parameter values at which some coordinate crosses an integer.  These divide the range [0,max] into subintervals.  We include 0 and max in the sequence to serve as endpoints of the outermost subintervals. */
   samplepoints := [(transitionpoints[i] + transitionpoints[i+1])/2 : i in [1..#transitionpoints-1]]; 
           /* the sequence of midpoints of the parameter subintervals */
   for s in samplepoints do
      samplevector := s*linearcoefficients + constantcoefficients;
      translationvector := 2 * RoundVector(1/2 * samplevector);
      translatedsamplevector := samplevector - translationvector; /* This has coordinates in [-1,1]. */
      newconstantcoefficients:=constantcoefficients - translationvector;
      newlinearcoefficients:=linearcoefficients;
      for i in [1..6] do
         if translatedsamplevector[i] lt 0 then 
            newconstantcoefficients[i] *:= -1;
            newlinearcoefficients[i] *:= -1;
         end if;
      end for;
          /* Now newlinearcoefficients *s + newconstantcoefficients should have entries in [0,1]. */
      dihedral6family := [newconstantcoefficients,newlinearcoefficients];
      if #Dihedral6FamilyRange(dihedral6family) eq 2 then
         Append(~output, AdjustDihedral6Range(dihedral6family));
      end if;
   end for;
   return output;
end function;


/* ----------------------------------------------------------------------- */

/* SatisfiabilityInterval(linears) assumes that linears is a sequence of linear polynomials a_i t + b_i, and returns the closed interval [c,d] on which they are all nonnegative.  If the interval is empty, then [c,d] with c > d is returned.  An error results if the interval in question is infinite.  */

function SatisfiabilityInterval(linears)
   lowerbounds := [];
   upperbounds := [];
   for lin in linears do
      a := MonomialCoefficient(lin,t);
      b := MonomialCoefficient(lin,1);
      if a gt 0 then Append(~lowerbounds,-b/a);
      elif a lt 0 then Append(~upperbounds,-b/a);
      elif b lt 0 then return [QQ!1,QQ!0];
      end if;
   end for;
   return [Max(lowerbounds),Min(upperbounds)];
end function;

/* ParametrizedMatrixInterval(pam) takes an AngleMatrix whose entries are linear polynomials in t, and returns the interval [c,d] on which the inequalities necessary and sufficient for it to come from a vector configuration are satisfied.  An error results if the interval in question is infinite or empty. */

/* AngleMatrixFamilyInterval(amf) is the same for an AngleMatrixFamily. */

/* SubspaceInterval(sub) is the same for a subspace of ATVs corresponding to a 1-parameter family of AngleMatrices. */

function ParametrizedMatrixInterval(pam)
   return SatisfiabilityInterval(AngleMatrixInequalities(pam,1));
end function;

function AngleMatrixFamilyInterval(amf)
   assert #amf eq 2;
   return ParametrizedMatrixInterval(MatrixFamilyToParametrizedMatrix(amf));
end function;

/* AdjustAngleMatrixFamily(amf) takes a 1-parameter AngleMatrixFamily, shifts the parameter to make the validity range be [0,q], and returns the resulting AngleMatrixFamily.  The value of q is returned as a second output. */

function AdjustAngleMatrixFamily(amf)
   assert #amf eq 2;
   int:=AngleMatrixFamilyInterval(amf);
   min:=Min(int);
   max:=Max(int);
   return [amf[1] + min*amf[2], amf[2]], max-min;
end function;

function SubspaceInterval(sub)
   assert Dimension(sub)-1 eq 1;
   return ParametrizedMatrixInterval(SubspaceToParametrizedMatrix(sub));
end function;

/* ----------------------------------------------------------------------- */
/* LINEAR TRANSFORMATIONS on TVs, ATVs, and ANGLE MATRICES */

/* TVRemoveRowColumn(tv,i), where tv is a vector of length n(n-1)/2, and 1 <= i <= n, converts tv to an n x n matrix, removes the i-th row and column, and converts it back to a vector of length (n-1)(n-2)/2. */

/* RemoveRowColumnLinearTransformation(n,i) is the matrix of the linear transformation TVRemoveRowColumn(-,i) from Q^{n(n-1)/2} to Q^{(n-1)(n-2)/2}, augmented by the 1 x 1 matrix (1) at upper left. */

function TVRemoveRowColumn(tv,i)
  mat:=TVToAngleMatrix(tv);
  mat2:=RemoveRowColumn(mat,i,i);
  return AngleMatrixToTV(mat2);  
end function;

function RemoveRowColumnLinearTransformation(n,i)
  N:=ExactQuotient(n*(n-1),2);
  mat:=Matrix(QQ,[Eltseq(TVRemoveRowColumn(StandardBasisElement(N,j),i)) : j in [1..N]]);
  return AugmentMatrix(1,mat);
end function;

/* TVMinorMatrix(tv,I), where tv is a vector of length n(n-1)/2, and I is a subset of {1,...,n}, converts tv to an n x n matrix, takes the minor whose rows and columns are indexed by I, and converts it back to a vector of length m(m-1)/2, where m is the size of I. */

/* MinorMatrixLinearTransformation(n,I) is the matrix of the linear transformation TVMinorMatrix(-,I) from Q^{n(n-1)/2} to Q^{m(m-1)/2}, augmented by the 1 x 1 matrix (1) at upper left. */

function TVMinorMatrix(tv,I)
  mat:=TVToAngleMatrix(tv);
  mat2:=MinorMatrix(mat,I);
  return AngleMatrixToTV(mat2);  
end function;

function MinorMatrixLinearTransformation(n,I)
  N:=ExactQuotient(n*(n-1),2);
  mat:=Matrix(QQ,[Eltseq(TVMinorMatrix(StandardBasisElement(N,j),I)) : j in [1..N]]);
  return AugmentMatrix(1,mat);
end function;

/* TVPermute(tv,g), where tv is a vector of length n(n-1)/2, and g is in S_n, converts tv to an matrix n x n matrix, permutes its rows and columns according to the permutation g, and converts it back to a vector of length n(n-1)/2. */

/* ATVPermute(atv,g), where atv is a vector of length 1 + n(n-1)/2, and g is in S_n, applies TVPermute(-,g) to all but the first coordinate of atv. */

/* PermuteLinearTransformation(n,g) is the matrix of the linear transformation TVPermute(-,g) from Q^{n(n-1)/2} to Q^{n(n-1)/2}, augmented by the 1 x 1 matrix (1) at upper left. */

/* ATVSymmetricGroup(n) is the group of all such matrices, isomorphic to S_n. */

function TVPermute(tv,g)
  mat:=TVToAngleMatrix(tv);
  mat2:=PermutationMatrix(QQ,Inverse(g))*mat*PermutationMatrix(QQ,g);
  return AngleMatrixToTV(mat2);  
end function;

function ATVPermute(atv,g)
  return AugmentVector(1,TVPermute(DiminishVector(atv),g));
end function;

function PermuteLinearTransformation(n,g)
  N:=ExactQuotient(n*(n-1),2);
  mat:=Matrix(QQ,[Eltseq(TVPermute(StandardBasisElement(N,j),g)) : j in [1..N]]);
  return AugmentMatrix(1,mat);
end function;

function ATVSymmetricGroup(n)
  N:= ExactQuotient(n*(n-1),2);
  Sn:=SymmetricGroup(n);
  return MatrixGroup<1+N,QQ | [PermuteLinearTransformation(n,g): g in Generators(Sn)]>;
end function;

/* ATVNegate(atv,I), where atv is a vector of length 1 + n(n-1)/2, and I is a subset of {1,...,n}, acts on the angles in the way that would result from negating v_i for i in I.  Namely, the angle between v_i and v_j is sent to pi minus itself (implemented as atv[1] minus itself) if exactly one of i and j belongs to I. */

/* NegateLinearTransformation(I) is the matrix of the linear transformation ATVNegate(-,I) from Q^{1+n(n-1)/2} to itself. */

function ATVNegate(atv,I)
  mat:=ATVToAngleMatrix(atv);
  n:=Ncols(mat);
  newmatrix:=Matrix( QQ, [ [((i in I) xor (j in I)) select atv[1]-mat[i,j] else mat[i,j] : j in [1..n]] : i in [1..n] ] );
  newtv:=AngleMatrixToTV(newmatrix);
  return AugmentVector(atv[1],newtv);
end function;

function NegateLinearTransformation(n,I)
   N:=ExactQuotient(n*(n-1),2);
   return Matrix( QQ, [ Eltseq(ATVNegate(StandardBasisElement(1+N,j),I)) : j in [1..1+N] ] );
end function;

/* ATVNegationGroup(n), with N := n(n-1)/2, is the image of {+-1}^n in GL_{1+N}(Q) describing the action of negating the n vectors independently. */
/* The results are stored in the list of groups NegationGroup. */

/* ATVSymmetricGroupNegations(n), with N := n(n-1)/2, is the image of S_n semidirect {+-1}^n in GL_{1+N}(Q). */
/* The results are stored in the sequence of groups ExplicitSymmetricGroupNegations. */

function ATVNegationGroup(n)
  N:= ExactQuotient(n*(n-1),2);
  return sub< GL(1+N,QQ) | {NegateLinearTransformation(n,{i}) : i in [1..n]} >;
end function;

ExplicitNegationGroups := [* ATVNegationGroup(n) : n in [1..maxsize] *];

/* ExplicitLastNegation is a list whose n-th element is the ATV transformation corresponding to negating the last row and last column. */

ExplicitLastNegation := [* NegateLinearTransformation(n,{n}) : n in [1..maxsize] *];


function ATVSymmetricGroupNegations(n)
  N:= ExactQuotient(n*(n-1),2);
  return sub< GL(1+N,QQ) | Generators(ATVSymmetricGroup(n)) join {NegateLinearTransformation(n,{1})} >;
end function;

ExplicitSymmetricGroupNegations := [* ATVSymmetricGroupNegations(n) : n in [1..maxsize] *];

/* Angle6Regge(angles), where angles is a 6-tuple of dihedral angles (possibly of a tetrahedron, but not necessarily) or a 6-tuple of pairwise angles between 4 vectors in R^3, applies the Regge involution fixing angles a_12 and a_34. */

/* TVRegge(tv) is the corresponding Regge involution on "tv" vectors. */

/* ATVReggeLinearTransformation is the matrix of the linear transformation TVRegge from Q^6 to Q^6, augmented by the 1 x 1 matrix (1) at upper left. */

function Angle6Regge(angles)
  seq:=Eltseq(angles);
  s:=(seq[3]+seq[4]+seq[5]+seq[6])/2;
  return Q6(seq[1],seq[2],s-seq[3],s-seq[4],s-seq[5],s-seq[6]); 
end function;

function TVRegge(tv)
  return Angle6ToTV(Angle6Regge(TVToAngle6(tv)));
end function;

ATVReggeLinearTransformation:=AugmentMatrix(1,Matrix(QQ,[Eltseq(TVRegge(StandardBasisElement(6,j))) : j in [1..6]]));

/* ATVS4 is S_4 viewed as subgroup of GL_7(Q). */
/* ATVS4Negations is the subgroup S_4^\pm of GL_7(Q) generated by S_4 and negations. */
/* ATVS4Regge is the subgroup R of GL_7(Q) generated by S_4 and the Regge involutions. */
/* ATVS4NegationsRegge is the subgroup R^\pm of GL_7(Q) generated by S_4, negations, and Regge involutions. */

ATVS4:=ATVSymmetricGroup(4);
ATVS4Negations:= ExplicitSymmetricGroupNegations[4];
ATVS4Regge:= sub< GL(7,QQ) | Generators(ATVSymmetricGroup(4)) join {ATVReggeLinearTransformation} >;
ATVS4NegationsRegge:= sub< GL(7,QQ) | Generators(ExplicitSymmetricGroupNegations[4]) join {ATVReggeLinearTransformation} >;


/* ----------------------------------------------------------------------- */
/* MORE SUBSPACE ROUTINES */

/* IsAffineSpaceEmpty(sub), where sub is a subspace of the space of ATVs, considers the associated projective subspace, and returns True if it is contained in the hyperplane at infinity. */

function IsAffineSpaceEmpty(sub)
   mat:=BasisMatrix(sub);
   return IsZero(Transpose(mat)[1]);
end function;

/* IsPlanarSubspace(sub) returns True if it corresponds to a configuration of vectors all lying in a plane. */

function IsPlanarSubspace(sub)
   return IsPlanarAngleMatrixFamily(SubspaceToAngleMatrixFamily(sub));
end function;

/* IsPlanarSubspace(sub) returns True if it corresponds to a configuration of vectors all lying in a plane. */

function IsPerpSubspace(sub)
   return IsPerpAngleMatrixFamily(SubspaceToAngleMatrixFamily(sub));
end function;

/* IsReasonable(sub), where sub is a subspace parametrizing ATVs, returns False if any of the following hold: sub is contained in the hyperplane at infinity, one of the angles is independent of the parameters and lies outside (0,1), the vectors lie in a plane, one of the vectors is perpendicular to all the others. */

function IsReasonable(sub);
   m:=Dimension(sub);
   if m eq 0 then return false; end if;
   for i in [2..m] do assert (sub.i)[1] eq 0; end for;
   if (sub.1)[1] eq 0 then return false; end if;
   sub1:=sub.1;
   n:=Ncols(sub1);
   assert sub1[1] eq 1;
   for j in [2..n] do
      if &and [(sub.i)[j] eq 0 : i in [2..m]] 
         then if (sub1[j] le 0) or (sub1[j] ge 1) then return false; end if;
      end if;
   end for;
   if IsPlanarSubspace(sub) then return false; end if;
   if IsPerpSubspace(sub) then return false; end if;
   return true;
end function;

/* IsSubfamily(n,sub1,sub2) returns True if subspace sub1 represents a subfamily of sub2, after acting on one or the other (it doesn't matter which) by an element of S_n semidirect {+-1}^n.  Both sub1 and sub2 should be parametrizing ATVs corresponding to n-tuples of vectors. */

function IsSubfamily(n,sub1,sub2)
   return &or [ s subset sub2 : s in Orbit(ExplicitSymmetricGroupNegations[n],sub1) ];
end function;

/* MinorSubspace(sub,I) takes a subspace mat parametrizing ATVs corresponding to n x n angle matrices, and a subset I of {1,...,n}, and returns the subspace parametrizing the ATVs corresponding to the I-principal minors of the angle matrices. */
/* MinorSubspaces(sub,m) returns the sequence of MinorSubspace(sub,I) as I ranges over m-elements subsets of {1,...,n}. */

function MinorSubspace(sub,I)
   ams:=SubspaceToAngleMatrixFamily(sub);
   return AngleMatrixFamilyToSubspace([MinorMatrix(ams[i],I): i in [1..#ams]]);
end function;

function MinorSubspaces(sub,m)
   n:=nOfSubspace(sub);
   return [MinorSubspace(sub,I) : I in Subsets({1..n},m)];
end function;


/* ----------------------------------------------------------------------- */
/* FINDING ORBIT REPRESENTATIVES */

/* FlipElements(seq) takes a sequence seq of rational numbers x in (0,1), replaces each x with min(x,1-x). */

function FlipElements(seq)
   return [Min(x,1-x) : x in seq];
end function;

/* SubspaceOrbitRepresentative(G,W) takes a finite subgroup G of GL(V) and a subspace W of V, and returns a distinguished representative of the G-orbit of W. */

function SubspaceOrbitRepresentative(G,W)
   if Dimension(W) eq 1 then
      Wvector := W.1;
      orbit := SetToSequence(Orbit(G,Wvector));
      min,position:=Min(orbit);
      return ATVToSubspace(orbit[position]);
   else
      orbit:=SetToSequence(Orbit(G,W));
      codes:=[Eltseq(EchelonMatrix(orbit[i])) : i in [1..#orbit]];
      min,position:=Min(codes);
      return orbit[position];
   end if;
end function;

/* ATVSymmetricGroupNegationsRepresentative(sub) takes a 1-dimensional subspace sub corresponding to a single n x n angle matrix, and returns, from the S_n semidirect {+-1}^n orbit of sub, the subspace whose associated ATV is lexicographically first. */

function ATVSymmetricGroupNegationsRepresentative(n,sub)
   if Dimension(sub) ne 1 then 
      return SubspaceOrbitRepresentative(ExplicitSymmetricGroupNegations[n],sub);
   end if;
   atv := sub.1;
   am := ATVToAngleMatrix(atv); 
   assert n eq Ncols(am);
   N:= ExactQuotient(n*(n-1),2);
   possibleatvs := {};
   tags := [FlipElements(Eltseq(am[i])) : i in [1..n]];
   sortedtags := [Sort(tag) : tag in tags];
   smallesttag := Min(sortedtags);
   for i in [1..n] do
       if sortedtags[i] eq smallesttag then 
          needflipping := { j : j in [1..n] | am[i,j] gt 1/2 };
          flippedatv := ATVNegate(atv,needflipping);
          discard,perm := Sort(tags[i],func<x,y|x-y>);
          newatv:=ATVPermute(flippedatv,perm^-1);
          smallesttagelements:=Sort(EliminateDuplicates(smallesttag));
          productofsymmetricgroups:=DirectProduct([SymmetricGroup(ElementFrequency(smallesttag,smallesttagelements[i])) : i in [1..#smallesttagelements]]);
          G:=MatrixGroup<1+N,QQ | [PermuteLinearTransformation(n,g): g in Generators(productofsymmetricgroups)] cat [NegateLinearTransformation(n,{i}) : i in [1..n] | smallesttag[i] eq 1/2]>;
          possibleatvs join:= Orbit(G,newatv);
       end if;
   end for;
   return ATVToSubspace(Min(possibleatvs));
end function;

/* ExpandedList(G,subspacelist) takes a finite subgroup G of GL(V) and a list of subspaces of V, and returns the union of the G-orbits of the subspaces, as a sequence of subspaces. */

function ExpandedList(G,subspacelist)
   return SetToSequence(&join [ Orbit(G,sub) : sub in subspacelist ] );
end function;

/* ATVSymmetricGroupNegationsRepresentatives(n,subspacelist) returns the sequence of distinguished S_n semidirect {+-1}^n orbit representatives for the subspaces in subspacelist, with duplicates removed.  Each subspace should parametrize ATVs corresponding to n x n AngleMatrices. */

function ATVSymmetricGroupNegationsRepresentatives(n,subspacelist)
   return EliminateDuplicates([ATVSymmetricGroupNegationsRepresentative(n,sub) : sub in subspacelist]);
end function;

/* ReggeRepresentatives(subspacelist) takes a list of subspaces parametrizing ATVs corresponding to 4 x 4 AngleMatrices, and returns a set of representatives for their orbits under the group ATVS4NegationsRegge. */

function ReggeRepresentatives(subspacelist)
   return EliminateDuplicates( [ SubspaceOrbitRepresentative(ATVS4NegationsRegge,sub) : sub in subspacelist ] );
end function;

/* NiceReggeRepresentative(sub) takes a subspace sub parametrizing ATVs corresponding to 4 x 4 AngleMatrices, and returns the 4 x 4 AngleMatrix in the ATVS4NegationsRegge-orbit that minimizes the sum of the denominators, and which among those is lexicographically smallest. */
function NiceReggeRepresentative(sub) 
   subspaceorbit:=SetToSequence(Orbit(ATVS4NegationsRegge,sub));
   TVorbit:=[SubspaceToTV(s) : s in subspaceorbit];
   denominatorsumsequence:=[DenominatorSum(tv):tv in TVorbit];
   min:=Min(denominatorsumsequence);
   minimizingTVs:=[TVorbit[i] : i in [1..#TVorbit] | denominatorsumsequence[i] eq min];
   bestTV:=Min(minimizingTVs);
   return TVToAngleMatrix(bestTV);
end function;


/* SubsetneqConjugate(sub1,sub2) takes subspaces sub1 and sub2 parametrizing ATVs corresponding to n x n AngleMatrices for the same n, and returns True if sub1 is strictly contained in an S_n semidirect {+-1}^n conjugate of sub2, or equivalently if some S_n semidirect {+-1}^n conjugate of sub1 is strictly contained in sub2. */

function SubsetneqConjugate(sub1,sub2)
   if Dimension(sub1) ge Dimension(sub2) then return false;
   else    
       n:=nOfSubspace(sub1);
       return &or [Subsetneq(sub1,sub) : sub in Orbit(ExplicitSymmetricGroupNegations[n],sub2)];
   end if;
end function;

/* EliminateSubconjugates(seq) takes a sequence of subspaces parametrizing ATVs corresponding to n x n AngleMatrices for the same n, and returns the sequence of those that are not strictly contained in a conjugate of another. */

function EliminateSubconjugates(seq);
   if IsEmpty(seq) then return seq; end if;
   n:=nOfSubspace(seq[1]);
   largesubs := [sub : sub in seq | Dimension(sub)-1 ge 1];
   largeconjugates := &join [Orbit(ExplicitSymmetricGroupNegations[n],sub) : sub in largesubs];
   return [ sub1 : sub1 in seq | not &or [Subsetneq(sub1,sub2):sub2 in largeconjugates] ];
end function;


/* ----------------------------------------------------------------------- */
/* NONDEGENERATE TETRAHEDRA */

sporadicTetrahedra:= [ 
< 60, [33, 33, 23, 17, 12, 24] >,
< 60, [33, 33, 26, 14, 15, 21] >,
< 60, [39, 27, 23, 17, 18, 18] >,
< 30, [18, 15, 10, 10, 6, 12] >,
< 60, [39, 27, 20, 20, 15, 21] >,
< 30, [18, 15, 13, 7, 9, 9] >,
< 60, [37, 33, 22, 22, 7, 17] >,
< 60, [35, 35, 27, 17, 10, 14] >,
< 30, [20, 15, 11, 11, 5, 7] >,
< 60, [35, 35, 24, 20, 7, 17] >,
< 30, [20, 15, 12, 10, 6, 6] >,
< 60, [37, 33, 27, 17, 12, 12] >,
< 30, [17, 13, 15, 10, 5, 11] >,
< 30, [18, 12, 15, 10, 6, 10] >,
< 60, [34, 26, 31, 19, 11, 21] >,
< 60, [35, 25, 29, 21, 10, 22] >,
< 60, [36, 24, 29, 21, 11, 21] >,
< 60, [35, 25, 31, 19, 12, 20] >,
< 60, [39, 21, 34, 14, 9, 33] >,
< 60, [39, 21, 36, 12, 11, 31] >,
< 30, [20, 10, 18, 6, 6, 15] >,
< 30, [21, 9, 17, 7, 6, 15] >,
< 60, [40, 20, 33, 15, 9, 33] >,
< 60, [42, 18, 33, 15, 11, 31] >,
< 30, [18, 9, 14, 11, 8, 13] >,
< 30, [16, 11, 17, 8, 9, 12] >,
< 30, [16, 11, 14, 11, 6, 15] >,
< 30, [15, 12, 17, 8, 8, 13] >,
< 30, [18, 9, 15, 10, 9, 12] >,
< 30, [15, 12, 15, 10, 6, 15] >,
< 60, [35, 25, 35, 15, 12, 24] >,
< 30, [18, 12, 15, 10, 4, 14] >,
< 60, [40, 20, 31, 19, 13, 23] >,
< 30, [20, 10, 15, 10, 6, 12] >,
< 60, [35, 25, 31, 19, 8, 28] >,
< 60, [36, 24, 35, 15, 13, 23] >,
< 30, [21, 9, 12, 12, 10, 10] >,
< 30, [15, 15, 12, 12, 4, 16] >,
< 30, [15, 15, 18, 6, 10, 10] >,
< 15, [10, 10, 4, 4, 2, 4] >,
< 15, [11, 9, 4, 4, 3, 3] >,
< 15, [10, 10, 5, 3, 3, 3] >,
< 15, [7, 7, 6, 6, 3, 7] >,
< 15, [9, 5, 6, 6, 5, 5] >,
< 15, [7, 7, 8, 4, 5, 5] >,
< 21, [15, 9, 7, 7, 6, 6] >,
< 21, [12, 12, 10, 4, 6, 6] >,
< 21, [12, 12, 7, 7, 3, 9] >,
< 30, [20, 15, 12, 6, 6, 12] >,
< 60, [41, 29, 23, 13, 12, 24] >,
< 12, [6, 4, 6, 4, 3, 6] >,
< 24, [12, 8, 13, 7, 7, 11] >,
< 24, [15, 13, 8, 6, 5, 9] >,
< 12, [8, 6, 4, 3, 3, 4] >,
< 60, [29, 25, 24, 20, 25, 19] >,
< 30, [15, 12, 12, 10, 12, 10] >,
< 30, [24, 15, 10, 6, 6, 10] >,
< 60, [43, 35, 20, 12, 7, 25] >,
< 15, [9, 9, 5, 5, 3, 3] > 
];

/* HillDihedral6Families contains the two 1-parameter Dihedral6Families of nondegenerate tetrahedra. */

HillDihedral6Families :=[
   [Q6(1/2, 1/2, 1, 1/3, 0, 0),
    Q6(0,   0,  -2,  0, 1, 1)],
   [Q6(5/6, 1/6, 2/3, 2/3, 0, 0),
    Q6(-1, 1, -1, -1, 1, 1)]
];

/* ----------------------------------------------------------------------- */
/* MINIMALLY DEGENERATE TETRAHEDRA */

/* Minimally degenerate means that three of the outward normals are pairwise independent vectors in a plane, and the fourth lies outside that plane. */

/* KedlayaDihedral6Families is a sequence containing the 1-parameter families of minimally degenerate tetrahedra, each expressed as a Dihedral6, except that the angles have not been adjusted to lie in the cube [0,1]^6. */

KedlayaDihedral6Families:=
[
[Q6(1/6, 5/6, 5/6, 1/6, 1/3, 0), Q6(3, 0, 2, -1, 0, 1)],
[Q6(0, 0, 2/3, 1, 4/3, 0), Q6(2, 2, 1, -3, 3, 1)],
[Q6(1/6, 5/6, 5/6, 1/6, 1/2, 0), Q6(2, 0, 1, -1, 0, 1)],
[Q6(1/6, 5/6, 5/6, 1/6, 0, 0), Q6(5, 1, 2, -2, 5, 1)],
[Q6(0, 0, 2/3, 1, 1, 0), Q6(3, 3, 0, -4, 5, 1)],
[Q6(1/6, 5/6, 5/6, 1/6, 1/3, 0), Q6(3, 1, 2, -2, 3, 1)],
[Q6(1/6, 0, 3/2, 1, 5/6, 0), Q6(2, 1, 1, -2, 2, 1)],
[Q6(1/6, 2/3, 5/6, 1/3, 1/6, 0), Q6(2, 1, 1, -2, 2, 1)],
[Q6(0, 0, 2/3, 1, 1, 0), Q6(1, 3, 0, -4, 1, 1)],
[Q6(0, 0, 2/3, 1, 2/3, 0), Q6(1, 2, 0, -3, 0, 1)],
[Q6(0, 0, 2/3, 1, 1/2, 0), Q6(1, 1, 0, -2, 0, 1)],
[Q6(1/3, 0, 1/2, 1, 1, 0), Q6(0, 2, 0, -3, 1, 1)]
];

/* perpDihedral6Family is the 2-parameter Dihedral6Family of degenerate tetrahedra in which vector 1 is perpendicular to vectors 2,3,4. */

perpDihedral6Family:=[Q6(1/2, 0, 1/2, 0, 1/2, 1), 
                      Q6(0, 1, 0, 0, 0, -1), 
                      Q6(0, 0, 0, 1, 0, -1)];

/* KedlayaDihedral6Families2 is a sequence containing the other 2-parameter families of minimally degenerate tetrahedra, each expressed as a Dihedral6, except that the angles have not been adjusted to lie in the cube [0,1]^6. */

KedlayaDihedral6Families2:=
[
   [Q6(0, 1, 0, 0, 1/2, 0), Q6(1, 0, 1, 0, 0, 0), Q6(0, 1, 0, 1, 0, -2)],
   [Q6(-1, 1/2, 3/2, 0, 0, 1/2), Q6(-1, -1, 2, 0, 1, 1), Q6(3, 1, -3, 1, 0, -2)]
];

/* --- */

KedlayaDihedral6FamiliesFixed:= &cat [FixKedlayaDihedral6Family(ked) : ked in KedlayaDihedral6Families];

/* RubinsteinDihedral6Families2Raw is the sequence of eight 2-parameter families of minimally degenerate tetrahedra, each expressed as a Dihedral6Family, except with each vector listed as a sequence, excluding the family in which one vector is perpendicular to all the others. */
/* RubinsteinDihedral6Families2 is the same, but with those sequences converted to vectors in Q^6. */
/* RubinsteinSubspaces2 is the sequence of the corresponding subspaces. */

RubinsteinDihedral6Families2Raw:=
[
[[1/2, 0, 0, 1/2, 1, 1/2], [0, 2, 1, -1, -1, -1], [0, 0, 2, 0, -2, 0]],
[[0, 1/2, 1, 1/2, 1/2, 0], [1, -1, -2, 0, 1, 1], [2, 0, -1, -1, -1, 1]],
[[0, 1/2, 1, 1/2, 1/2, 0], [1, -1, -1, -1, 0, 2], [2, 0, -2, 0, 0, 0]],
[[0, 1/2, 1/2, 0, 1, 1/2], [1, -1, 0, 2, -1, -1], [2, 0, 0, 0, -2, 0]],
[[0, 1/2, 1/2, 0, 1, 1/2], [1, -1, 1, 1, -2, 0], [2, 0, -1, 1, -1, -1]],
[[0, 1/2, 1/2, 1, 0, 1/2], [1, -1, -1, -1, 2, 0], [2, 0, 0, -2, 0, 0]],
[[0, 1/2, 0, 1/2, 1/2, 1], [1, -1, 1, 1, 0, -2], [2, 0, 1, -1, -1, -1]],
[[0, 1/2, 0, 1/2, 1/2, 1], [0, 0, 2, 0, 0, -2], [2, 0, 1, -1, -1, -1]]
];

RubinsteinDihedral6Families1Raw:=
[
[[2/3, 1/2, 1/2, 1/3, 0, 1/2],[0, -3, 1, 0, 2, 1]],
[[2/3, 1, 2/3, 0, 0, 0],[0, -3, 0, 1, 1, 2]],
[[2/3, 2/3, 1/3, 0, 1/3, 1/3],[0, 1, 0, -3, -1, 2]],
[[2/3, 2/3, 1/3, 0, 1/3, 1/3],[-1, 2, 0, -3, 0, 1]],
[[1/2, 1/2, 1/2, 1/2, 1/3, 0],[-1, 1, -1, 3, 0, -4]],
[[1/3, 1/3, 5/6, 1/6, 1/2, 1/2],[2, 2, -3, 1, -1, -3]],
[[1/2, 1/3, 2/3, 1/2, 0, 1/2],[1, 0, 0, -3, 2, 1]],
[[1/2, 1/2, 1/3, 1/3, 1/6, 5/6],[-3, 3, -4, 0, 1, 5]],
[[1/3, 2/3, 2/3, 0, 2/3, 1/3],[2, -2, -1, 3, -3, -1]],
[[1/2, 1/2, 2/3, 0, 1/2, 1/2],[-3, 3, 0, -4, 5, 1]],
[[2/3, 0, 2/3, 1, 0, 0],[0, 1, 0, -3, 1, 2]],
[[2/3, 2/3, 1/3, 1/3, 0, 1/3],[0, 4, -1, -1, -3, -1]],
[[2/3, 2/3, 1/3, 1/3, 1/3, 0],[0, 4, -1, -1, -1, -3]],
[[2/3, 1, 0, 0, 0, 1],[0, -4, 3, 3, 1, -5]],
[[1/2, 1/2, 1/2, 1/2, 0, 1/3],[-5, 1, 3, 3, -4, 0]],
[[2/3, 1, 0, 0, 1, 0],[0, -4, 3, 3, -5, 1]],
[[1/2, 1/2, 1/2, 1/2, 1/3, 0],[-5, 1, 3, 3, 0, -4]],
[[2/3, 2/3, 0, 1/3, 1/3, 1/3],[0, -1, 3, 0, -2, 1]],
[[2/3, 2/3, 1/3, 1/3, 1/3, 0],[0, 1, -1, 2, 0, -3]],
[[2/3, 2/3, 1/3, 1/3, 1/3, 0],[-1, 2, 0, 1, 0, -3]],
[[2/3, 2/3, 0, 1/3, 1/3, 1/3],[1, -2, 3, 0, -1, 0]],
[[2/3, 1, 0, 0, 0, 2/3],[1, -3, 2, 2, 1, -3]],
[[2/3, 1, 0, 0, 2/3, 0],[1, -3, 2, 2, -3, 1]],
[[5/6, 1/2, 1/3, 1/3, 1/6, 1/6],[1, -3, 0, 4, -1, -1]],
[[1/3, 1/3, 1/2, 1/2, 1/6, 5/6],[-1, -1, 0, 1, 0, 2]],
[[1/3, 1/3, 1/2, 1/2, 5/6, 1/6],[-1, -1, 0, 1, 2, 0]],
[[1/3, 1/3, 5/6, 1/6, 1/2, 1/2],[-2, -2, 3, -1, 3, 1]],
[[1/2, 1/2, 1/3, 1/3, 1/6, 5/6],[0, -1, 1, 1, 0, -2]],
[[1/2, 1/2, 1/3, 1/3, 5/6, 1/6],[0, -1, 1, 1, -2, 0]],
[[1/2, 0, 2/3, 1, 0, 0],[0, -1, 0, 2, -1, -1]],
[[1/2, 0, 0, 0, 1, 2/3],[0, 1, 1, 1, -2, 0]],
[[1/2, 0, 0, 0, 2/3, 1],[0, 1, 1, 1, 0, -2]],
[[1/2, 1/6, 1/6, 1/6, 2/3, 2/3],[0, 1, 2, 0, -1, -1]],
[[1/3, 2/3, 1/2, 1/6, 5/6, 1/6],[-1, 1, 0, -1, 2, 0]],
[[1/2, 1/2, 1/2, 1/2, 1/3, 0],[-1, 1, 0, 1, 0, -2]],
[[1/3, 2/3, 1/6, 1/6, 1/2, 1/2],[-1, 1, -2, 0, 1, 0]],
[[1/3, 2/3, 1/2, 1/2, 1/6, 1/6],[2, -2, 1, -3, 1, 3]],
[[1/2, 1/2, 1/2, 1/2, 0, 1/3],[-1, -1, 0, 3, -2, 0]],
[[1/2, 1/2, 1/2, 1/2, 1/3, 0],[-1, -1, 0, 3, 0, -2]],
[[1/2, 1/3, 5/6, 1/3, 1/6, 1/3],[1, 0, -2, -1, 0, 3]],
[[1/2, 1/6, 5/6, 1/6, 1/3, 2/3],[1, 2, -2, 1, -2, -1]],
[[1/2, 1/6, 2/3, 1/3, 1/6, 5/6],[1, 2, 0, -1, 0, -3]],
[[1/2, 1/2, 2/3, 0, 1/2, 1/2],[1, -1, 0, 2, -3, 0]],
[[1/2, 2/3, 1/2, 1/3, 1/2, 0],[-2, 1, 2, 1, 1, -2]],
[[1/2, 2/3, 2/3, 1/6, 1/3, 1/6],[-2, 1, 3, 0, 0, -1]],
[[2/3, 1, 1/2, 0, 0, 0],[0, -2, 0, 1, 1, 1]],
[[2/3, 1/3, 1/2, 1/6, 1/6, 5/6],[0, 1, -1, -2, 0, 3]],
[[1/3, 1/3, 1/2, 1/2, 1/6, 5/6],[3, 1, -1, -1, 0, -4]],
[[1/3, 1/3, 1/2, 1/2, 5/6, 1/6],[3, 1, -1, -1, -4, 0]],
[[1/3, 1/3, 5/6, 1/6, 1/2, 1/2],[3, 1, -3, 1, -2, -2]],
[[2/3, 0, 1/2, 1, 0, 0],[0, -2, 0, 3, -1, -1]],
[[2/3, 2/3, 1/6, 1/6, 1/2, 1/6],[0, -1, 3, 0, -2, 1]],
[[2/3, 1/2, 1/6, 1/3, 2/3, 1/6],[0, 1, 2, -1, -3, 0]],
[[1/2, 1/3, 2/3, 1/2, 0, 1/2],[2, -1, -1, -2, 2, 1]],
[[1/2, 1/3, 5/6, 1/3, 1/6, 1/3],[2, -1, -2, -1, 1, 2]],
[[1/2, 1/2, 0, 1/3, 1/2, 1/2],[-1, 1, -2, 0, 1, 0]],
[[1/2, 1/6, 2/3, 1/3, 1/6, 5/6],[2, 1, -1, 0, 0, -3]],
[[2/3, 1/3, 2/3, 1/3, 0, 1/2],[-1, 1, 2, 0, -3, 0]],
[[1/2, 1/6, 5/6, 1/6, 1/3, 2/3],[2, 1, -2, 1, -1, -2]],
[[2/3, 1/3, 2/3, 0, 1/3, 2/3],[-1, 1, -1, -3, 4, 0]],
[[1/2, 2/3, 1/3, 1/6, 2/3, 1/6],[2, -1, 0, 1, -3, 0]],
[[1/2, 2/3, 1/2, 0, 1/2, 1/3],[2, -1, -1, 2, -2, -1]],
[[2/3, 2/3, 1/2, 1/6, 1/6, 1/6],[-1, 2, 2, -1, -2, -1]],
[[2/3, 2/3, 1/3, 0, 1/3, 1/3],[-1, -1, 1, -3, 4, 0]],
[[2/3, 2/3, 1/3, 0, 1/3, 1/3],[-1, -1, 1, -3, 0, 4]],
[[2/3, 1/3, 2/3, 0, 1/3, 2/3],[-2, 2, -1, -3, 3, 1]],
[[2/3, 2/3, 1/6, 1/6, 1/2, 1/6],[1, -2, 2, 1, -2, 1]],
[[2/3, 2/3, 1/3, 0, 1/3, 1/3],[-3, 1, 1, -3, 2, 2]],
[[1/3, 1/3, 1/3, 0, 2/3, 2/3],[1, 1, 1, 3, -4, 0]],
[[1/3, 1/3, 1/3, 0, 2/3, 2/3],[1, 1, 1, 3, 0, -4]],
[[1/2, 1/2, 1/2, 1/2, 0, 2/3],[-3, 3, 1, 5, -4, 0]],
[[1/3, 2/3, 1/6, 1/6, 1/2, 1/2],[2, -2, 3, 1, -3, 1]],
[[1/2, 1/2, 5/6, 1/6, 1/3, 1/3],[-3, 3, 5, 1, 0, -4]],
[[1/2, 1/3, 1/2, 0, 1/2, 2/3],[1, 0, 1, 2, -3, 0]],
[[1/2, 1/2, 0, 1/3, 1/2, 1/2],[1, -1, 4, 0, -3, 1]],
[[2/3, 0, 0, 0, 1, 2/3],[0, 1, 2, 1, -3, 0]],
[[2/3, 1/3, 5/6, 1/6, 1/6, 1/2],[-2, 2, 3, 1, -1, -3]],
[[2/3, 2/3, 1/3, 1/3, 0, 1/3],[-1, -1, 0, 4, -3, 1]],
[[2/3, 2/3, 1/3, 1/3, 1/3, 0],[-1, -1, 0, 4, 1, -3]],
[[1/3, 1/3, 1/3, 0, 2/3, 2/3],[3, -1, 1, 3, -2, -2]],
[[5/6, 1/6, 1/2, 1/6, 1/3, 2/3],[-1, 1, 3, 1, -4, 0]],
[[5/6, 1/2, 1/6, 1/6, 1/3, 1/3],[-1, 3, 1, 1, -4, 0]],
[[5/6, 1/2, 1/6, 1/6, 1/3, 1/3],[-1, 3, 1, 1, 0, -4]],
[[2/3, 1, 2/3, 0, 0, 0],[-1, 3, 3, -1, -2, -2]],
[[5/6, 1/6, 2/3, 1/3, 1/6, 1/2],[1, -1, 0, 4, -1, -3]],
[[2/3, 1/3, 1/2, 1/6, 1/6, 5/6],[2, -2, 3, 1, -1, -3]],
[[2/3, 2/3, 1/3, 1/3, 0, 1/3],[-3, 1, 2, 2, -3, 1]],
[[2/3, 2/3, 1/3, 1/3, 1/3, 0],[-3, 1, 2, 2, 1, -3]],
[[1/3, 1/3, 5/6, 1/2, 1/6, 1/6],[1, 1, -3, -1, 0, 4]],
[[1/3, 1/3, 5/6, 1/2, 1/6, 1/6],[1, 1, -3, -1, 4, 0]],
[[1/3, 1/3, 2/3, 2/3, 0, 1/3],[1, 1, 0, -4, 3, 1]],
[[1/3, 1/3, 2/3, 2/3, 1/3, 0],[1, 1, 0, -4, 1, 3]],
[[1/3, 2/3, 1/2, 1/2, 1/6, 1/6],[-1, 1, 0, 1, 0, -2]],
[[1/2, 1/2, 1/2, 1/2, 0, 2/3],[-1, 1, 0, 3, -2, 0]],
[[1/2, 1/2, 2/3, 1/3, 1/6, 1/6],[-1, 1, 3, -1, -4, 0]],
[[1/2, 1/2, 1/3, 1/3, 1/6, 5/6],[-2, 2, -5, 1, 1, 5]],
[[1/2, 1/2, 2/3, 1/3, 1/6, 1/6],[-2, 2, 3, -1, -3, -1]],
[[1/2, 1/2, 2/3, 1/3, 1/6, 1/6],[-2, -2, 5, 1, 1, -5]],
[[1/2, 1/2, 2/3, 1/3, 1/6, 1/6],[-2, -2, 5, 1, -5, 1]],
[[1/2, 1/3, 1/3, 1/6, 1/3, 5/6],[1, 0, 3, 0, -1, -2]],
[[1/2, 1/2, 1/6, 1/6, 2/3, 1/3],[1, -1, 4, 0, -3, 1]],
[[1/2, 5/6, 1/6, 1/6, 1/3, 1/3],[1, -2, 2, 1, -2, 1]],
[[1/2, 5/6, 1/6, 1/6, 1/3, 1/3],[1, -2, 3, 0, -1, 0]],
[[2/3, 1/6, 1/3, 1/6, 1/2, 2/3],[0, 1, 3, 0, -2, -1]],
[[1/3, 1/3, 2/3, 2/3, 0, 1/3],[3, -1, -2, -2, 3, 1]],
[[1/3, 1/3, 2/3, 2/3, 1/3, 0],[3, -1, -2, -2, 1, 3]],
[[1/3, 1/3, 5/6, 1/2, 1/6, 1/6],[3, -1, -3, -1, 2, 2]],
[[2/3, 1/3, 1/2, 1/6, 1/6, 5/6],[-1, 1, -4, 0, 1, 3]],
[[1/2, 1/2, 2/3, 1/3, 1/6, 1/6],[-5, 1, 5, 1, -2, -2]],
[[2/3, 2/3, 1/2, 1/6, 1/6, 1/6],[-1, -1, 4, 0, 1, -3]],
[[2/3, 2/3, 1/2, 1/6, 1/6, 1/6],[-1, -1, 4, 0, -3, 1]],
[[1/2, 1/3, 1/3, 1/6, 1/3, 5/6],[2, -1, 2, 1, -1, -2]],
[[1/2, 1/3, 1/2, 0, 1/2, 2/3],[2, -1, 1, 2, -2, -1]],
[[1/2, 1/2, 1/6, 1/6, 2/3, 1/3],[2, -2, 3, 1, -3, 1]],
[[5/6, 1/6, 1/3, 1/3, 1/2, 1/2],[2, -2, -5, 1, 5, 1]],
[[2/3, 1/3, 1/2, 0, 1/3, 2/3],[1, -1, 0, 3, 0, -2]],
[[5/6, 1/6, 1/2, 1/6, 1/3, 2/3],[1, -1, -4, 0, 3, 1]],
[[2/3, 2/3, 1/2, 1/6, 1/6, 1/6],[-3, 1, 4, 0, -1, -1]],
[[2/3, 1/3, 2/3, 1/3, 0, 2/3],[-1, 1, 0, 4, -3, -1]],
[[2/3, 1/3, 2/3, 1/3, 0, 2/3],[-2, 2, 1, 3, -3, -1]],
[[1/3, 1/3, 1/6, 1/6, 1/2, 5/6],[1, 1, 4, 0, -1, -3]],
[[1/3, 1/3, 1/6, 1/6, 5/6, 1/2],[1, 1, 4, 0, -3, -1]],
[[1/2, 1/2, 1/3, 2/3, 1/6, 1/6],[-1, 1, -1, 3, 0, -4]],
[[2/3, 1/3, 1/6, 1/6, 1/2, 1/2],[0, -4, -5, 1, 3, 3]],
[[1/2, 1/2, 1/3, 2/3, 1/6, 1/6],[-2, 2, -1, 3, -1, -3]],
[[2/3, 1/3, 5/6, 1/6, 1/6, 1/2],[-1, 1, 3, 1, 0, -4]],
[[1/3, 1/3, 1/6, 1/6, 1/2, 5/6],[3, -1, 2, 2, -1, -3]],
[[1/3, 1/3, 1/6, 1/6, 5/6, 1/2],[3, -1, 2, 2, -3, -1]],
[[2/3, 2/3, 1/6, 1/6, 1/6, 1/2],[1, 1, 3, -1, 0, -4]],
[[2/3, 2/3, 1/6, 1/6, 1/2, 1/6],[1, 1, 3, -1, -4, 0]],
[[5/6, 1/6, 2/3, 1/3, 1/6, 1/2],[1, -1, 1, 3, 0, -4]],
[[1/2, 1/2, 1/3, 0, 1/2, 1/2],[-5, 1, 0, -4, 3, 3]],
[[2/3, 2/3, 1/6, 1/6, 1/6, 1/2],[3, -1, 1, 1, 0, -4]],
[[2/3, 2/3, 1/6, 1/6, 1/2, 1/6],[3, -1, 1, 1, -4, 0]],
[[1/2, 1/2, 5/6, 1/6, 1/3, 1/3],[-2, 2, 5, 1, 1, -5]],
[[1/2, 1/2, 1/3, 0, 1/2, 1/2],[1, 1, 0, 2, -3, 0]],
[[1/2, 1/2, 1/3, 0, 1/2, 1/2],[1, 1, 0, 2, 0, -3]],
[[2/3, 0, 0, 0, 1, 1/2],[0, 2, 1, 1, -3, 0]],
[[2/3, 0, 0, 0, 1/2, 1],[0, 2, 1, 1, 0, -3]],
[[5/6, 1/6, 1/2, 1/2, 1/3, 1/3],[2, -2, 1, 5, 1, -5]],
[[1/2, 1/2, 1/6, 1/6, 1/3, 2/3],[2, 2, 5, -1, -1, -5]],
[[1/2, 1/2, 1/6, 1/6, 2/3, 1/3],[2, 2, 5, -1, -5, -1]],
[[1/2, 1/2, 1/6, 1/6, 1/3, 2/3],[5, -1, 2, 2, -1, -5]],
[[1/2, 1/2, 1/6, 1/6, 2/3, 1/3],[5, -1, 2, 2, -5, -1]]
];

RubinsteinDihedral6s0Raw:=
[
[7/15, 2/5, 3/5, 4/15, 4/15, 8/15],
[3/5, 4/15, 7/15, 2/5, 4/15, 8/15],
[3/5, 7/15, 7/15, 4/15, 2/5, 4/15],
[3/5, 8/15, 3/5, 2/15, 1/3, 1/3],
[2/3, 1/3, 8/15, 2/5, 2/15, 2/5],
[2/3, 1/3, 3/5, 1/3, 1/5, 1/3],
[11/15, 1/5, 4/5, 2/15, 2/15, 11/15],
[4/5, 2/15, 11/15, 1/5, 2/15, 11/15],
[4/5, 1/3, 2/5, 1/3, 1/3, 1/3],
[4/5, 11/15, 4/15, 2/15, 1/5, 2/15],
[7/15, 2/5, 17/30, 3/10, 7/30, 17/30],
[7/15, 13/30, 3/5, 7/30, 3/10, 1/2],
[1/2, 13/30, 7/15, 13/30, 1/10, 11/15],
[1/2, 13/30, 23/30, 2/15, 2/5, 13/30],
[8/15, 11/30, 3/5, 3/10, 1/6, 3/5],
[8/15, 11/30, 2/3, 7/30, 7/30, 8/15],
[8/15, 13/30, 1/2, 11/30, 1/10, 11/15],
[8/15, 13/30, 3/5, 7/30, 7/30, 1/2],
[8/15, 1/2, 7/15, 11/30, 1/10, 3/5],
[8/15, 1/2, 8/15, 11/30, 1/10, 2/5],
[8/15, 1/2, 3/5, 3/10, 1/6, 1/3],
[8/15, 1/2, 2/3, 1/6, 3/10, 2/5],
[17/30, 3/10, 7/15, 2/5, 7/30, 17/30],
[17/30, 3/10, 3/5, 4/15, 11/30, 13/30],
[17/30, 1/3, 3/5, 3/10, 2/15, 7/10],
[17/30, 1/3, 11/15, 1/6, 4/15, 17/30],
[17/30, 2/5, 19/30, 4/15, 1/6, 1/2],
[17/30, 2/5, 23/30, 2/15, 3/10, 1/2],
[17/30, 13/30, 3/5, 1/3, 1/10, 13/30],
[17/30, 13/30, 19/30, 3/10, 2/15, 2/5],
[17/30, 7/15, 13/30, 2/5, 1/10, 3/5],
[17/30, 7/15, 1/2, 3/10, 2/5, 7/30],
[17/30, 7/15, 1/2, 13/30, 4/15, 1/10],
[17/30, 7/15, 17/30, 4/15, 1/6, 7/15],
[17/30, 7/15, 2/3, 1/6, 1/3, 11/30],
[17/30, 1/2, 7/15, 3/10, 2/15, 17/30],
[17/30, 1/2, 8/15, 3/10, 2/15, 13/30],
[17/30, 1/2, 17/30, 4/15, 1/6, 2/5],
[17/30, 1/2, 3/5, 1/6, 4/15, 13/30],
[17/30, 8/15, 13/30, 4/15, 1/6, 8/15],
[17/30, 8/15, 1/2, 7/30, 2/5, 7/30],
[17/30, 8/15, 1/2, 11/30, 4/15, 1/10],
[17/30, 8/15, 8/15, 1/6, 4/15, 13/30],
[17/30, 17/30, 2/5, 1/3, 1/10, 17/30],
[17/30, 17/30, 2/5, 1/3, 17/30, 1/10],
[17/30, 17/30, 3/5, 2/15, 3/10, 11/30],
[17/30, 17/30, 3/5, 2/15, 11/30, 3/10],
[3/5, 4/15, 17/30, 3/10, 11/30, 13/30],
[3/5, 3/10, 8/15, 11/30, 1/6, 3/5],
[3/5, 3/10, 17/30, 1/3, 2/15, 7/10],
[3/5, 3/10, 2/3, 7/30, 3/10, 7/15],
[3/5, 3/10, 11/15, 1/6, 3/10, 8/15],
[3/5, 13/30, 7/15, 13/30, 1/10, 2/5],
[3/5, 13/30, 1/2, 3/10, 11/30, 4/15],
[3/5, 13/30, 1/2, 13/30, 7/30, 2/15],
[3/5, 13/30, 3/5, 3/10, 7/30, 4/15],
[3/5, 7/15, 13/30, 3/10, 13/30, 7/30],
[3/5, 8/15, 11/30, 11/30, 1/10, 17/30],
[3/5, 8/15, 11/30, 11/30, 17/30, 1/10],
[3/5, 17/30, 1/2, 1/6, 11/30, 4/15],
[3/5, 17/30, 1/2, 3/10, 7/30, 2/15],
[19/30, 4/15, 13/30, 2/5, 3/10, 1/2],
[19/30, 11/30, 8/15, 2/5, 1/10, 13/30],
[19/30, 11/30, 19/30, 3/10, 1/5, 1/3],
[19/30, 13/30, 13/30, 3/10, 2/5, 4/15],
[19/30, 7/15, 11/30, 1/3, 1/6, 8/15],
[19/30, 7/15, 1/2, 7/30, 1/3, 3/10],
[19/30, 7/15, 1/2, 4/15, 1/10, 3/5],
[19/30, 7/15, 1/2, 11/30, 1/5, 1/6],
[19/30, 7/15, 8/15, 1/6, 1/3, 11/30],
[19/30, 7/15, 19/30, 2/15, 7/30, 7/15],
[19/30, 1/2, 7/15, 3/10, 1/15, 19/30],
[19/30, 1/2, 8/15, 3/10, 1/15, 11/30],
[19/30, 1/2, 17/30, 4/15, 1/10, 1/3],
[19/30, 1/2, 2/3, 1/10, 4/15, 13/30],
[19/30, 8/15, 2/5, 3/10, 2/5, 1/6],
[19/30, 8/15, 7/15, 7/30, 1/3, 7/30],
[19/30, 8/15, 1/2, 1/6, 1/3, 3/10],
[19/30, 8/15, 1/2, 4/15, 1/10, 2/5],
[19/30, 8/15, 1/2, 3/10, 1/5, 1/6],
[19/30, 8/15, 8/15, 7/30, 2/15, 11/30],
[2/3, 7/30, 8/15, 11/30, 7/30, 8/15],
[2/3, 7/30, 3/5, 3/10, 3/10, 7/15],
[2/3, 3/10, 7/15, 11/30, 7/30, 1/2],
[2/3, 3/10, 8/15, 11/30, 1/6, 1/2],
[2/3, 11/30, 7/15, 11/30, 1/6, 7/15],
[2/3, 11/30, 7/15, 13/30, 1/6, 1/3],
[2/3, 11/30, 8/15, 11/30, 7/30, 4/15],
[2/3, 11/30, 17/30, 4/15, 4/15, 11/30],
[2/3, 13/30, 7/15, 3/10, 1/10, 3/5],
[2/3, 13/30, 19/30, 2/15, 4/15, 13/30],
[2/3, 17/30, 2/5, 3/10, 3/10, 2/15],
[2/3, 17/30, 13/30, 4/15, 4/15, 1/6],
[7/10, 11/30, 19/30, 1/6, 2/15, 3/5],
[7/10, 2/5, 3/5, 7/30, 1/15, 17/30],
[7/10, 2/5, 2/3, 1/6, 2/15, 1/2],
[7/10, 7/15, 2/5, 3/10, 1/3, 7/30],
[7/10, 7/15, 13/30, 1/3, 1/10, 2/5],
[7/10, 7/15, 1/2, 7/30, 1/15, 19/30],
[7/10, 7/15, 8/15, 7/30, 1/5, 3/10],
[7/10, 7/15, 17/30, 2/15, 1/6, 1/2],
[7/10, 8/15, 2/5, 3/10, 4/15, 1/6],
[7/10, 8/15, 1/2, 1/6, 2/15, 13/30],
[7/10, 8/15, 1/2, 7/30, 1/15, 11/30],
[7/10, 3/5, 2/5, 7/30, 1/15, 13/30],
[7/10, 3/5, 1/2, 2/15, 1/6, 1/3],
[7/10, 19/30, 11/30, 1/6, 2/15, 2/5],
[7/10, 19/30, 2/5, 2/15, 1/6, 11/30],
[11/15, 1/6, 17/30, 1/3, 4/15, 17/30],
[11/15, 1/6, 3/5, 3/10, 3/10, 8/15],
[11/15, 1/5, 23/30, 1/6, 1/10, 23/30],
[11/15, 11/30, 11/30, 1/3, 4/15, 13/30],
[11/15, 11/30, 13/30, 4/15, 1/3, 11/30],
[11/15, 11/30, 17/30, 4/15, 1/15, 17/30],
[11/15, 11/30, 2/3, 1/6, 1/6, 7/15],
[11/15, 2/5, 17/30, 1/6, 1/10, 19/30],
[11/15, 2/5, 19/30, 1/10, 1/6, 17/30],
[11/15, 13/30, 13/30, 1/3, 2/15, 11/30],
[11/15, 13/30, 1/2, 4/15, 1/5, 3/10],
[11/15, 13/30, 3/5, 1/6, 1/10, 1/2],
[11/15, 13/30, 2/3, 1/10, 1/6, 1/2],
[11/15, 17/30, 11/30, 4/15, 1/15, 13/30],
[11/15, 17/30, 1/2, 1/10, 1/6, 2/5],
[11/15, 17/30, 1/2, 2/15, 1/5, 3/10],
[11/15, 17/30, 1/2, 1/6, 1/10, 1/3],
[11/15, 3/5, 13/30, 1/6, 1/10, 11/30],
[23/30, 1/6, 11/15, 1/5, 1/10, 23/30],
[23/30, 1/6, 4/5, 2/15, 1/6, 7/10],
[23/30, 4/15, 13/30, 2/5, 3/10, 2/5],
[23/30, 4/15, 7/15, 11/30, 1/3, 11/30],
[23/30, 3/10, 17/30, 7/30, 2/15, 3/5],
[23/30, 3/10, 19/30, 1/6, 1/5, 8/15],
[23/30, 1/3, 2/3, 1/6, 1/15, 19/30],
[23/30, 1/3, 7/10, 2/15, 1/10, 3/5],
[23/30, 11/30, 8/15, 1/5, 1/10, 19/30],
[23/30, 11/30, 19/30, 1/10, 1/5, 8/15],
[23/30, 7/15, 1/2, 1/6, 1/5, 11/30],
[23/30, 7/15, 1/2, 7/30, 2/15, 3/10],
[23/30, 8/15, 1/2, 1/10, 1/5, 11/30],
[23/30, 8/15, 1/2, 1/6, 2/15, 3/10],
[23/30, 17/30, 3/10, 7/30, 2/15, 2/5],
[23/30, 17/30, 2/5, 2/15, 7/30, 3/10],
[23/30, 2/3, 1/3, 1/6, 1/15, 11/30],
[23/30, 2/3, 2/5, 1/10, 2/15, 3/10],
[4/5, 2/15, 23/30, 1/6, 1/6, 7/10],
[4/5, 1/6, 1/2, 11/30, 11/30, 7/15],
[4/5, 1/6, 8/15, 11/30, 3/10, 1/2],
[4/5, 3/10, 7/15, 3/10, 7/30, 7/15],
[4/5, 3/10, 1/2, 4/15, 4/15, 13/30],
[4/5, 3/10, 17/30, 4/15, 2/15, 1/2],
[4/5, 3/10, 3/5, 7/30, 1/6, 7/15],
[4/5, 3/10, 19/30, 1/5, 1/15, 19/30],
[4/5, 3/10, 7/10, 2/15, 2/15, 17/30],
[4/5, 1/3, 11/30, 11/30, 3/10, 11/30],
[4/5, 1/3, 11/30, 11/30, 11/30, 3/10],
[4/5, 11/30, 7/15, 7/30, 1/6, 1/2],
[4/5, 11/30, 8/15, 7/30, 1/10, 1/2],
[4/5, 8/15, 3/10, 7/30, 1/6, 11/30],
[4/5, 8/15, 11/30, 1/6, 7/30, 3/10],
[4/5, 8/15, 11/30, 7/30, 1/10, 11/30],
[4/5, 8/15, 13/30, 1/6, 1/6, 3/10],
[4/5, 19/30, 3/10, 1/5, 1/15, 11/30],
[4/5, 19/30, 2/5, 1/10, 1/6, 4/15],
[4/5, 11/15, 7/30, 1/6, 7/30, 1/10],
[5/6, 1/5, 4/5, 1/10, 1/15, 23/30],
[5/6, 4/15, 19/30, 1/5, 1/10, 3/5],
[5/6, 4/15, 2/3, 1/6, 2/15, 17/30],
[5/6, 3/10, 8/15, 1/5, 1/6, 17/30],
[5/6, 3/10, 17/30, 1/6, 1/5, 8/15],
[5/6, 7/15, 11/30, 4/15, 1/6, 1/3],
[5/6, 7/15, 2/5, 7/30, 1/5, 3/10],
[5/6, 7/10, 7/30, 1/6, 1/5, 2/15],
[5/6, 4/5, 1/5, 1/10, 1/15, 7/30],
[5/6, 4/5, 7/30, 1/15, 1/10, 1/5],
[13/15, 1/6, 23/30, 2/15, 1/15, 23/30],
[13/15, 1/6, 4/5, 1/10, 1/10, 11/15],
[13/15, 3/10, 1/2, 7/30, 7/30, 7/15],
[13/15, 3/10, 8/15, 7/30, 1/6, 1/2],
[13/15, 17/30, 3/10, 1/5, 2/15, 3/10],
[13/15, 17/30, 1/3, 1/6, 1/6, 4/15],
[13/15, 23/30, 1/6, 2/15, 1/15, 7/30],
[13/15, 23/30, 7/30, 1/15, 2/15, 1/6],
[9/10, 11/15, 1/6, 2/15, 1/10, 1/5],
[9/10, 11/15, 1/5, 1/10, 2/15, 1/6],
[1/2, 17/42, 19/42, 8/21, 4/7, 3/14],
[1/2, 17/42, 25/42, 5/21, 3/7, 5/14],
[11/21, 19/42, 11/21, 5/14, 5/42, 4/7],
[11/21, 19/42, 2/3, 3/14, 11/42, 3/7],
[23/42, 8/21, 1/2, 17/42, 3/7, 3/14],
[23/42, 3/7, 23/42, 8/21, 1/14, 13/21],
[23/42, 3/7, 31/42, 4/21, 11/42, 3/7],
[23/42, 1/2, 19/42, 8/21, 1/14, 5/7],
[23/42, 1/2, 23/42, 8/21, 1/14, 2/7],
[23/42, 1/2, 4/7, 5/14, 2/21, 11/42],
[23/42, 1/2, 31/42, 2/21, 5/14, 3/7],
[23/42, 11/21, 10/21, 5/14, 3/7, 5/42],
[23/42, 11/21, 4/7, 11/42, 1/3, 3/14],
[4/7, 5/14, 1/2, 17/42, 17/42, 5/21],
[4/7, 17/42, 10/21, 17/42, 5/42, 4/7],
[4/7, 17/42, 11/21, 17/42, 1/14, 13/21],
[4/7, 17/42, 2/3, 3/14, 13/42, 8/21],
[4/7, 17/42, 31/42, 4/21, 2/7, 17/42],
[4/7, 23/42, 19/42, 8/21, 8/21, 1/14],
[4/7, 23/42, 4/7, 11/42, 11/42, 4/21],
[25/42, 3/7, 23/42, 5/21, 1/6, 4/7],
[25/42, 3/7, 25/42, 4/21, 3/14, 11/21],
[25/42, 10/21, 3/7, 17/42, 3/7, 5/42],
[25/42, 10/21, 4/7, 11/42, 2/7, 11/42],
[25/42, 11/21, 3/7, 17/42, 8/21, 1/14],
[25/42, 11/21, 4/7, 11/42, 5/21, 3/14],
[25/42, 4/7, 19/42, 5/21, 1/6, 3/7],
[25/42, 4/7, 10/21, 3/14, 4/21, 17/42],
[13/21, 19/42, 1/2, 13/42, 1/14, 5/7],
[13/21, 19/42, 4/7, 3/14, 1/6, 1/2],
[13/21, 23/42, 1/2, 1/6, 3/14, 3/7],
[13/21, 23/42, 1/2, 13/42, 1/14, 2/7],
[9/14, 8/21, 4/7, 11/42, 2/21, 29/42],
[9/14, 8/21, 5/7, 5/42, 5/21, 23/42],
[9/14, 3/7, 25/42, 5/21, 5/42, 1/2],
[9/14, 3/7, 31/42, 2/21, 11/42, 1/2],
[9/14, 4/7, 17/42, 5/21, 5/42, 1/2],
[9/14, 4/7, 1/2, 11/42, 2/21, 11/42],
[9/14, 13/21, 3/7, 11/42, 2/21, 13/42],
[9/14, 13/21, 19/42, 5/21, 5/42, 2/7],
[2/3, 5/14, 10/21, 13/42, 1/6, 4/7],
[2/3, 5/14, 23/42, 2/7, 2/21, 29/42],
[2/3, 5/14, 25/42, 4/21, 2/7, 19/42],
[2/3, 5/14, 5/7, 5/42, 11/42, 11/21],
[29/42, 8/21, 3/7, 17/42, 1/3, 3/14],
[29/42, 8/21, 10/21, 5/14, 2/7, 11/42],
[29/42, 3/7, 25/42, 5/21, 1/14, 10/21],
[29/42, 3/7, 13/21, 3/14, 2/21, 19/42],
[29/42, 10/21, 5/14, 1/3, 1/6, 3/7],
[29/42, 10/21, 10/21, 3/14, 2/7, 13/42],
[29/42, 10/21, 1/2, 1/6, 2/7, 5/14],
[29/42, 10/21, 1/2, 13/42, 1/7, 3/14],
[29/42, 11/21, 5/14, 2/7, 5/42, 1/2],
[29/42, 11/21, 1/2, 11/42, 1/7, 3/14],
[29/42, 4/7, 17/42, 5/21, 1/14, 11/21],
[29/42, 4/7, 23/42, 2/21, 3/14, 8/21],
[5/7, 11/42, 10/21, 17/42, 11/42, 3/7],
[5/7, 11/42, 11/21, 5/14, 13/42, 8/21],
[5/7, 13/42, 10/21, 13/42, 3/14, 11/21],
[5/7, 13/42, 23/42, 5/21, 2/7, 19/42],
[5/7, 5/14, 10/21, 13/42, 1/6, 1/2],
[5/7, 5/14, 11/21, 13/42, 5/42, 1/2],
[5/7, 17/42, 3/7, 17/42, 11/42, 4/21],
[5/7, 17/42, 19/42, 8/21, 5/21, 3/14],
[5/7, 19/42, 5/14, 1/3, 4/21, 17/42],
[5/7, 19/42, 19/42, 5/21, 2/7, 13/42],
[5/7, 23/42, 5/14, 1/3, 2/21, 13/42],
[5/7, 23/42, 8/21, 11/42, 1/14, 11/21],
[5/7, 23/42, 19/42, 5/21, 4/21, 3/14],
[5/7, 23/42, 23/42, 2/21, 5/21, 5/14],
[31/42, 8/21, 23/42, 2/7, 1/14, 10/21],
[31/42, 8/21, 13/21, 3/14, 1/7, 17/42],
[31/42, 11/21, 5/14, 1/3, 5/42, 2/7],
[31/42, 11/21, 3/7, 11/42, 4/21, 3/14],
[16/21, 3/14, 11/21, 17/42, 11/42, 3/7],
[16/21, 3/14, 23/42, 8/21, 2/7, 17/42],
[16/21, 5/14, 23/42, 2/7, 2/21, 19/42],
[16/21, 5/14, 25/42, 5/21, 1/7, 17/42],
[17/21, 3/14, 23/42, 2/7, 5/21, 23/42],
[17/21, 3/14, 4/7, 11/42, 11/42, 11/21],
[5/6, 2/7, 5/7, 5/42, 1/21, 29/42],
[5/6, 2/7, 31/42, 2/21, 1/14, 2/3],
[5/6, 5/7, 2/7, 5/42, 1/21, 13/42],
[5/6, 5/7, 1/3, 1/14, 2/21, 11/42],
[6/7, 3/14, 1/2, 13/42, 13/42, 10/21],
[6/7, 3/14, 11/21, 13/42, 11/42, 1/2],
[6/7, 11/42, 29/42, 1/7, 1/21, 29/42],
[6/7, 11/42, 31/42, 2/21, 2/21, 9/14],
[6/7, 17/42, 8/21, 11/42, 3/14, 8/21],
[6/7, 17/42, 17/42, 5/21, 5/21, 5/14],
[6/7, 29/42, 11/42, 1/7, 1/21, 13/42],
[6/7, 29/42, 1/3, 1/14, 5/42, 5/21],
[37/42, 5/21, 29/42, 1/7, 1/14, 2/3],
[37/42, 5/21, 5/7, 5/42, 2/21, 9/14],
[19/21, 9/14, 11/42, 1/7, 2/21, 11/42],
[19/21, 9/14, 2/7, 5/42, 5/42, 5/21],
[9/20, 9/20, 17/30, 4/15, 17/60, 1/2],
[9/20, 9/20, 17/30, 4/15, 1/2, 17/60],
[7/15, 13/30, 31/60, 19/60, 13/60, 7/12],
[29/60, 9/20, 29/60, 5/12, 1/10, 11/15],
[29/60, 9/20, 23/30, 2/15, 23/60, 9/20],
[1/2, 29/60, 9/20, 9/20, 1/15, 23/30],
[1/2, 29/60, 9/20, 9/20, 23/30, 1/15],
[1/2, 29/60, 4/5, 1/10, 5/12, 5/12],
[8/15, 13/30, 11/20, 17/60, 11/60, 11/20],
[8/15, 13/30, 3/4, 7/60, 7/20, 29/60],
[11/20, 7/20, 13/30, 2/5, 13/60, 7/12],
[11/20, 7/20, 3/5, 7/30, 23/60, 5/12],
[11/20, 5/12, 29/60, 23/60, 1/10, 11/15],
[11/20, 5/12, 3/4, 7/60, 11/30, 7/15],
[11/20, 9/20, 1/2, 17/60, 13/30, 4/15],
[11/20, 9/20, 1/2, 23/60, 1/15, 23/30],
[11/20, 9/20, 1/2, 29/60, 7/30, 1/15],
[11/20, 9/20, 17/30, 4/15, 11/60, 1/2],
[11/20, 29/60, 31/60, 5/12, 4/15, 1/10],
[11/20, 29/60, 11/20, 23/60, 7/30, 2/15],
[11/20, 11/20, 13/30, 4/15, 11/60, 1/2],
[11/20, 11/20, 13/30, 4/15, 1/2, 11/60],
[11/20, 11/20, 1/2, 23/60, 1/15, 7/30],
[11/20, 11/20, 1/2, 23/60, 7/30, 1/15],
[17/30, 2/5, 11/20, 7/20, 1/12, 43/60],
[17/30, 2/5, 37/60, 17/60, 3/20, 31/60],
[17/30, 7/15, 29/60, 19/60, 5/12, 13/60],
[17/30, 7/15, 11/20, 23/60, 13/60, 3/20],
[17/30, 8/15, 9/20, 17/60, 9/20, 11/60],
[17/30, 8/15, 31/60, 7/20, 1/4, 7/60],
[7/12, 11/30, 17/30, 19/60, 1/10, 3/4],
[7/12, 11/30, 23/30, 7/60, 3/10, 11/20],
[7/12, 23/60, 8/15, 11/30, 1/12, 43/60],
[7/12, 23/60, 23/30, 2/15, 19/60, 29/60],
[7/12, 2/5, 17/30, 7/20, 1/15, 41/60],
[7/12, 2/5, 23/30, 3/20, 4/15, 29/60],
[7/12, 5/12, 1/2, 17/60, 2/5, 3/10],
[7/12, 5/12, 1/2, 29/60, 1/5, 1/10],
[7/12, 5/12, 3/5, 3/10, 7/60, 1/2],
[7/12, 5/12, 4/5, 1/10, 19/60, 1/2],
[7/12, 13/30, 3/5, 7/20, 1/15, 23/60],
[7/12, 13/30, 19/30, 19/60, 1/10, 7/20],
[7/12, 17/30, 2/5, 7/20, 1/15, 37/60],
[7/12, 17/30, 13/20, 1/10, 19/60, 11/30],
[7/12, 7/12, 2/5, 3/10, 7/60, 1/2],
[7/12, 7/12, 2/5, 3/10, 1/2, 7/60],
[7/12, 7/12, 1/2, 19/60, 1/10, 1/5],
[7/12, 7/12, 1/2, 19/60, 1/5, 1/10],
[3/5, 3/10, 5/12, 5/12, 17/60, 1/2],
[3/5, 3/10, 5/12, 5/12, 1/2, 17/60],
[3/5, 7/20, 11/20, 1/3, 1/10, 3/4],
[3/5, 7/20, 23/30, 7/60, 19/60, 8/15],
[3/5, 23/60, 11/20, 11/30, 1/15, 41/60],
[3/5, 23/60, 23/30, 3/20, 17/60, 7/15],
[3/5, 13/30, 9/20, 7/20, 5/12, 13/60],
[3/5, 13/30, 31/60, 5/12, 13/60, 3/20],
[3/5, 11/20, 23/60, 11/30, 1/15, 37/60],
[3/5, 11/20, 13/20, 1/10, 1/3, 7/20],
[3/5, 17/30, 23/60, 17/60, 29/60, 3/20],
[3/5, 17/30, 9/20, 7/20, 17/60, 1/12],
[3/5, 7/12, 13/30, 7/20, 19/60, 1/15],
[3/5, 7/12, 31/60, 4/15, 7/30, 3/20],
[37/60, 7/20, 7/15, 11/30, 11/60, 11/20],
[37/60, 7/20, 3/5, 7/30, 19/60, 5/12],
[37/60, 5/12, 9/20, 7/20, 2/5, 7/30],
[37/60, 5/12, 29/60, 19/60, 11/30, 4/15],
[37/60, 9/20, 5/12, 7/20, 2/15, 17/30],
[37/60, 9/20, 3/5, 1/6, 19/60, 23/60],
[37/60, 29/60, 9/20, 5/12, 4/15, 1/10],
[37/60, 29/60, 31/60, 7/20, 1/5, 1/6],
[19/30, 4/15, 31/60, 19/60, 23/60, 5/12],
[19/30, 23/60, 11/20, 2/5, 1/15, 23/60],
[19/30, 23/60, 19/30, 19/60, 3/20, 3/10],
[19/30, 7/15, 7/20, 7/20, 11/60, 1/2],
[19/30, 7/15, 7/20, 7/20, 1/2, 11/60],
[19/30, 7/15, 23/60, 7/20, 9/20, 11/60],
[19/30, 7/15, 9/20, 5/12, 1/4, 7/60],
[19/30, 7/15, 1/2, 23/60, 3/20, 3/20],
[19/30, 8/15, 7/20, 19/60, 29/60, 3/20],
[19/30, 8/15, 7/20, 7/20, 7/60, 1/2],
[19/30, 8/15, 7/20, 7/20, 1/2, 7/60],
[19/30, 8/15, 5/12, 23/60, 17/60, 1/12],
[19/30, 8/15, 1/2, 19/60, 3/20, 3/20],
[19/30, 11/20, 2/5, 23/60, 19/60, 1/15],
[19/30, 11/20, 31/60, 4/15, 1/5, 11/60],
[19/30, 7/12, 13/30, 19/60, 1/4, 1/10],
[19/30, 7/12, 9/20, 3/10, 7/30, 7/60],
[13/20, 19/60, 8/15, 11/30, 3/20, 31/60],
[13/20, 19/60, 19/30, 4/15, 1/12, 3/4],
[13/20, 19/60, 19/30, 4/15, 1/4, 5/12],
[13/20, 19/60, 47/60, 7/60, 7/30, 3/5],
[13/20, 7/20, 7/15, 11/30, 11/60, 1/2],
[13/20, 7/20, 8/15, 11/30, 7/60, 1/2],
[13/20, 5/12, 9/20, 23/60, 2/15, 13/30],
[13/20, 5/12, 17/30, 4/15, 1/4, 19/60],
[13/20, 29/60, 9/20, 19/60, 1/15, 19/30],
[13/20, 29/60, 2/3, 1/10, 17/60, 5/12],
[2/3, 3/10, 11/20, 17/60, 19/60, 5/12],
[2/3, 3/10, 37/60, 17/60, 1/12, 3/4],
[2/3, 3/10, 37/60, 17/60, 1/4, 5/12],
[2/3, 3/10, 47/60, 7/60, 1/4, 7/12],
[2/3, 7/20, 11/20, 2/5, 1/10, 7/20],
[2/3, 7/20, 3/5, 7/20, 3/20, 3/10],
[2/3, 11/20, 2/5, 7/20, 1/4, 1/10],
[2/3, 11/20, 9/20, 3/10, 1/5, 3/20],
[41/60, 23/60, 9/20, 23/60, 1/6, 2/5],
[41/60, 23/60, 8/15, 3/10, 1/4, 19/60],
[41/60, 5/12, 23/60, 7/20, 2/5, 7/30],
[41/60, 5/12, 9/20, 17/60, 1/3, 3/10],
[41/60, 9/20, 29/60, 7/20, 1/15, 11/30],
[41/60, 9/20, 17/30, 4/15, 3/20, 17/60],
[41/60, 29/60, 5/12, 23/60, 7/30, 2/15],
[41/60, 29/60, 9/20, 7/20, 1/5, 1/6],
[41/60, 8/15, 2/5, 7/20, 7/30, 7/60],
[41/60, 8/15, 13/30, 19/60, 1/5, 3/20],
[41/60, 13/20, 11/30, 4/15, 1/4, 1/12],
[41/60, 13/20, 2/5, 7/30, 13/60, 7/60],
[7/10, 7/20, 19/30, 11/60, 7/60, 19/30],
[7/10, 7/20, 2/3, 3/20, 3/20, 3/5],
[7/10, 7/15, 31/60, 11/60, 7/60, 11/20],
[7/10, 7/15, 13/20, 1/12, 13/60, 29/60],
[7/10, 8/15, 29/60, 11/60, 7/60, 9/20],
[7/10, 8/15, 31/60, 13/60, 1/12, 7/20],
[7/10, 13/20, 11/30, 11/60, 7/60, 11/30],
[7/10, 13/20, 2/5, 3/20, 3/20, 1/3],
[43/60, 1/4, 43/60, 11/60, 1/10, 11/15],
[43/60, 1/4, 23/30, 2/15, 3/20, 41/60],
[43/60, 2/5, 7/12, 1/6, 7/60, 3/5],
[43/60, 2/5, 37/60, 2/15, 3/20, 17/30],
[43/60, 5/12, 29/60, 7/20, 1/10, 1/3],
[43/60, 5/12, 8/15, 3/10, 3/20, 17/60],
[43/60, 13/30, 17/30, 11/60, 1/10, 11/20],
[43/60, 13/30, 3/5, 3/20, 2/15, 31/60],
[43/60, 9/20, 29/60, 1/4, 1/15, 19/30],
[43/60, 9/20, 13/20, 1/12, 7/30, 7/15],
[43/60, 7/15, 2/5, 23/60, 7/30, 3/20],
[43/60, 7/15, 13/30, 7/20, 1/5, 11/60],
[43/60, 17/30, 13/30, 11/60, 1/10, 9/20],
[43/60, 17/30, 29/60, 2/15, 3/20, 2/5],
[43/60, 3/5, 5/12, 1/6, 7/60, 2/5],
[43/60, 3/5, 13/30, 3/20, 2/15, 23/60],
[43/60, 37/60, 1/3, 3/10, 1/4, 1/12],
[43/60, 37/60, 2/5, 7/30, 11/60, 3/20],
[11/15, 13/30, 11/20, 13/60, 1/20, 37/60],
[11/15, 13/30, 7/12, 11/60, 1/12, 31/60],
[11/15, 17/30, 5/12, 11/60, 1/12, 29/60],
[11/15, 17/30, 9/20, 13/60, 1/20, 23/60],
[3/4, 13/60, 41/60, 13/60, 1/10, 11/15],
[3/4, 13/60, 23/30, 2/15, 11/60, 13/20],
[3/4, 3/10, 7/12, 7/30, 7/60, 19/30],
[3/4, 3/10, 2/3, 3/20, 1/5, 11/20],
[3/4, 19/60, 5/12, 7/20, 4/15, 13/30],
[3/4, 19/60, 7/15, 3/10, 19/60, 23/60],
[3/4, 5/12, 7/20, 19/60, 11/30, 4/15],
[3/4, 5/12, 23/60, 17/60, 1/3, 3/10],
[3/4, 5/12, 7/15, 7/30, 7/60, 11/20],
[3/4, 5/12, 8/15, 7/30, 1/20, 37/60],
[3/4, 5/12, 17/30, 2/15, 13/60, 9/20],
[3/4, 5/12, 2/3, 1/10, 11/60, 29/60],
[3/4, 29/60, 9/20, 17/60, 1/15, 11/30],
[3/4, 29/60, 31/60, 13/60, 2/15, 3/10],
[3/4, 7/12, 1/3, 3/10, 13/60, 7/60],
[3/4, 7/12, 11/30, 4/15, 11/60, 3/20],
[3/4, 43/60, 17/60, 11/60, 4/15, 1/10],
[3/4, 43/60, 19/60, 3/20, 7/30, 2/15],
[23/30, 7/20, 8/15, 13/60, 7/60, 3/5],
[23/30, 7/20, 37/60, 2/15, 1/5, 31/60],
[23/30, 23/60, 31/60, 7/30, 1/10, 11/20],
[23/30, 23/60, 3/5, 3/20, 11/60, 7/15],
[23/30, 7/15, 5/12, 1/4, 7/60, 9/20],
[23/30, 7/15, 9/20, 17/60, 1/12, 7/20],
[23/30, 31/60, 23/60, 7/30, 1/10, 9/20],
[23/30, 31/60, 29/60, 2/15, 1/5, 7/20],
[23/30, 8/15, 23/60, 13/60, 1/12, 29/60],
[23/30, 8/15, 5/12, 1/4, 1/20, 23/60],
[23/30, 7/12, 3/10, 1/4, 7/60, 11/30],
[23/30, 7/12, 2/5, 3/20, 13/60, 4/15],
[47/60, 3/20, 7/15, 13/30, 23/60, 9/20],
[47/60, 3/20, 29/60, 5/12, 2/5, 13/30],
[47/60, 4/15, 7/12, 7/30, 3/20, 3/5],
[47/60, 4/15, 19/30, 11/60, 1/5, 11/20],
[47/60, 23/60, 8/15, 7/30, 1/12, 31/60],
[47/60, 23/60, 3/5, 1/6, 1/20, 13/20],
[47/60, 23/60, 3/5, 1/6, 3/20, 9/20],
[47/60, 23/60, 41/60, 1/12, 2/15, 17/30],
[47/60, 9/20, 5/12, 1/4, 2/15, 13/30],
[47/60, 9/20, 29/60, 11/60, 1/5, 11/30],
[47/60, 8/15, 7/20, 7/30, 7/60, 2/5],
[47/60, 8/15, 13/30, 3/20, 1/5, 19/60],
[47/60, 37/60, 2/5, 1/6, 1/20, 7/20],
[47/60, 37/60, 13/30, 2/15, 1/12, 19/60],
[47/60, 41/60, 1/4, 13/60, 4/15, 1/10],
[47/60, 41/60, 19/60, 3/20, 1/5, 1/6],
[4/5, 3/20, 11/20, 1/3, 3/10, 11/20],
[4/5, 3/20, 17/30, 19/60, 19/60, 8/15],
[4/5, 1/6, 29/60, 23/60, 7/20, 29/60],
[4/5, 1/6, 11/20, 7/20, 19/60, 29/60],
[4/5, 1/6, 41/60, 13/60, 3/20, 41/60],
[4/5, 1/6, 43/60, 11/60, 11/60, 13/20],
[4/5, 11/60, 11/20, 11/30, 4/15, 29/60],
[4/5, 11/60, 17/30, 7/20, 17/60, 7/15],
[4/5, 19/60, 8/15, 13/60, 3/20, 17/30],
[4/5, 19/60, 7/12, 1/6, 1/5, 31/60],
[4/5, 7/20, 31/60, 7/30, 2/15, 31/60],
[4/5, 7/20, 17/30, 11/60, 11/60, 7/15],
[4/5, 11/30, 31/60, 11/60, 13/60, 9/20],
[4/5, 11/30, 7/12, 11/60, 1/20, 13/20],
[4/5, 11/30, 7/12, 11/60, 3/20, 9/20],
[4/5, 11/30, 41/60, 1/12, 3/20, 11/20],
[4/5, 31/60, 7/20, 7/30, 2/15, 23/60],
[4/5, 31/60, 5/12, 1/6, 1/5, 19/60],
[4/5, 11/20, 3/10, 1/4, 3/20, 1/3],
[4/5, 11/20, 11/30, 11/60, 13/60, 4/15],
[49/60, 3/20, 37/60, 17/60, 7/30, 3/5],
[49/60, 3/20, 19/30, 4/15, 1/4, 7/12],
[49/60, 7/20, 13/20, 7/60, 1/15, 19/30],
[49/60, 7/20, 2/3, 1/10, 1/12, 37/60],
[49/60, 7/15, 23/60, 7/30, 3/20, 2/5],
[49/60, 7/15, 13/30, 11/60, 1/5, 7/20],
[49/60, 29/60, 5/12, 1/4, 1/10, 1/3],
[49/60, 29/60, 9/20, 13/60, 2/15, 3/10],
[49/60, 7/12, 11/30, 1/5, 1/20, 7/20],
[49/60, 7/12, 13/30, 2/15, 7/60, 17/60],
[49/60, 13/20, 1/4, 13/60, 7/30, 2/15],
[49/60, 13/20, 17/60, 11/60, 1/5, 1/6],
[49/60, 13/20, 7/20, 7/60, 1/15, 11/30],
[49/60, 13/20, 23/60, 1/12, 1/10, 1/3],
[17/20, 3/20, 1/2, 23/60, 11/30, 7/15],
[17/20, 3/20, 8/15, 11/30, 19/60, 1/2],
[17/20, 17/60, 9/20, 19/60, 4/15, 13/30],
[17/20, 17/60, 7/15, 3/10, 17/60, 5/12],
[17/20, 3/10, 23/60, 11/30, 19/60, 11/30],
[17/20, 3/10, 2/5, 7/20, 1/3, 7/20],
[17/20, 19/60, 37/60, 3/20, 1/15, 19/30],
[17/20, 19/60, 2/3, 1/10, 7/60, 7/12],
[17/20, 9/20, 23/60, 13/60, 1/6, 2/5],
[17/20, 9/20, 5/12, 11/60, 1/5, 11/30],
[17/20, 11/20, 11/30, 1/5, 1/12, 19/60],
[17/20, 11/20, 2/5, 1/6, 7/60, 17/60],
[17/20, 37/60, 19/60, 3/20, 1/15, 11/30],
[17/20, 37/60, 23/60, 1/12, 2/15, 3/10],
[13/15, 3/10, 29/60, 1/4, 13/60, 29/60],
[13/15, 3/10, 11/20, 13/60, 11/60, 29/60],
[13/15, 3/10, 37/60, 3/20, 1/12, 37/60],
[13/15, 3/10, 13/20, 7/60, 7/60, 7/12],
[53/60, 17/60, 7/12, 11/60, 2/15, 17/30],
[53/60, 17/60, 3/5, 1/6, 3/20, 11/20],
[53/60, 7/12, 19/60, 3/20, 1/10, 1/3],
[53/60, 7/12, 7/20, 7/60, 2/15, 3/10],
[41/84, 5/12, 13/28, 31/84, 4/7, 3/14],
[41/84, 5/12, 25/42, 5/21, 37/84, 29/84],
[43/84, 5/12, 15/28, 31/84, 3/7, 3/14],
[43/84, 5/12, 47/84, 29/84, 17/42, 5/21],
[23/42, 8/21, 47/84, 29/84, 31/84, 23/84],
[47/84, 41/84, 37/84, 11/28, 1/14, 5/7],
[47/84, 41/84, 31/42, 2/21, 31/84, 5/12],
[4/7, 5/14, 15/28, 31/84, 31/84, 23/84],
[17/28, 37/84, 41/84, 37/84, 1/14, 2/7],
[17/28, 37/84, 4/7, 5/14, 13/84, 17/84],
[13/21, 19/42, 47/84, 19/84, 13/84, 43/84],
[13/21, 19/42, 61/84, 1/12, 25/84, 41/84],
[13/21, 23/42, 37/84, 19/84, 13/84, 41/84],
[13/21, 23/42, 43/84, 25/84, 1/12, 23/84],
[53/84, 23/84, 19/42, 8/21, 37/84, 29/84],
[53/84, 23/84, 13/28, 31/84, 3/7, 5/14],
[53/84, 5/12, 41/84, 37/84, 2/21, 11/42],
[53/84, 5/12, 23/42, 8/21, 13/84, 17/84],
[53/84, 37/84, 41/84, 9/28, 1/14, 5/7],
[53/84, 37/84, 61/84, 1/12, 13/42, 10/21],
[9/14, 3/7, 15/28, 25/84, 5/84, 59/84],
[9/14, 3/7, 17/28, 19/84, 11/84, 41/84],
[9/14, 4/7, 13/28, 25/84, 5/84, 25/84],
[9/14, 4/7, 43/84, 11/84, 19/84, 11/28],
[55/84, 5/12, 11/21, 13/42, 5/84, 59/84],
[55/84, 5/12, 31/42, 2/21, 23/84, 41/84],
[19/28, 41/84, 37/84, 31/84, 1/14, 2/7],
[19/28, 41/84, 43/84, 25/84, 1/7, 3/14],
[29/42, 10/21, 31/84, 25/84, 13/84, 41/84],
[29/42, 10/21, 37/84, 31/84, 1/12, 23/84],
[29/42, 11/21, 5/12, 29/84, 5/84, 25/84],
[29/42, 11/21, 43/84, 11/84, 23/84, 29/84],
[59/84, 31/84, 10/21, 13/42, 13/84, 43/84],
[59/84, 31/84, 4/7, 3/14, 1/4, 5/12],
[59/84, 31/84, 25/42, 5/21, 5/84, 61/84],
[59/84, 31/84, 3/4, 1/12, 3/14, 4/7],
[59/84, 53/84, 17/42, 5/21, 5/84, 23/84],
[59/84, 53/84, 3/7, 3/14, 1/12, 1/4],
[5/7, 5/14, 47/84, 19/84, 1/4, 5/12],
[5/7, 5/14, 7/12, 1/4, 5/84, 61/84],
[5/7, 5/14, 17/28, 19/84, 17/84, 5/12],
[5/7, 5/14, 3/4, 1/12, 19/84, 47/84],
[61/84, 29/84, 11/21, 13/42, 11/84, 41/84],
[61/84, 29/84, 25/42, 5/21, 17/84, 5/12],
[61/84, 41/84, 5/12, 29/84, 2/21, 11/42],
[61/84, 41/84, 13/28, 25/84, 1/7, 3/14],
[3/4, 5/12, 31/84, 25/84, 3/14, 3/7],
[3/4, 5/12, 37/84, 19/84, 2/7, 5/14],
[3/4, 7/12, 5/14, 2/7, 5/84, 23/84],
[3/4, 7/12, 3/7, 3/14, 11/84, 17/84],
[65/84, 25/84, 19/28, 13/84, 1/14, 5/7],
[65/84, 25/84, 31/42, 2/21, 11/84, 55/84],
[65/84, 47/84, 5/14, 2/7, 1/12, 1/4],
[65/84, 47/84, 17/42, 5/21, 11/84, 17/84],
[65/84, 59/84, 9/28, 13/84, 1/14, 2/7],
[65/84, 59/84, 29/84, 11/84, 2/21, 11/42],
[67/84, 23/84, 55/84, 5/28, 1/14, 5/7],
[67/84, 23/84, 31/42, 2/21, 13/84, 53/84],
[67/84, 5/12, 5/14, 2/7, 19/84, 11/28],
[67/84, 5/12, 17/42, 5/21, 23/84, 29/84],
[23/28, 55/84, 23/84, 17/84, 1/14, 2/7],
[23/28, 55/84, 29/84, 11/84, 1/7, 3/14],
[71/84, 17/84, 37/84, 11/28, 5/14, 3/7],
[71/84, 17/84, 19/42, 8/21, 31/84, 5/12],
[71/84, 53/84, 23/84, 17/84, 2/21, 11/42],
[71/84, 53/84, 9/28, 13/84, 1/7, 3/14],
[6/7, 3/14, 41/84, 9/28, 25/84, 41/84],
[6/7, 3/14, 15/28, 25/84, 23/84, 41/84],
[6/7, 3/14, 55/84, 5/28, 11/84, 55/84],
[6/7, 3/14, 19/28, 13/84, 13/84, 53/84],
[73/84, 17/84, 7/12, 1/4, 3/14, 4/7],
[73/84, 17/84, 25/42, 5/21, 19/84, 47/84],
[49/90, 16/45, 26/45, 5/18, 8/45, 59/90],
[49/90, 16/45, 2/3, 17/90, 4/15, 17/30],
[3/5, 3/10, 47/90, 1/3, 8/45, 59/90],
[3/5, 3/10, 2/3, 17/90, 29/90, 23/45],
[11/18, 22/45, 43/90, 14/45, 7/90, 28/45],
[11/18, 22/45, 2/3, 11/90, 4/15, 13/30],
[11/18, 23/45, 47/90, 14/45, 7/90, 17/45],
[11/18, 23/45, 17/30, 4/15, 11/90, 1/3],
[28/45, 41/90, 26/45, 29/90, 1/18, 16/45],
[28/45, 41/90, 3/5, 3/10, 7/90, 1/3],
[28/45, 49/90, 19/45, 29/90, 1/18, 29/45],
[28/45, 49/90, 2/3, 7/90, 3/10, 2/5],
[19/30, 7/15, 41/90, 1/3, 7/90, 28/45],
[19/30, 7/15, 2/3, 11/90, 13/45, 37/90],
[19/30, 8/15, 37/90, 1/3, 1/18, 29/45],
[19/30, 8/15, 2/3, 7/90, 14/45, 7/18],
[29/45, 49/90, 19/45, 5/18, 31/90, 8/45],
[29/45, 49/90, 13/30, 4/15, 1/3, 17/90],
[59/90, 1/3, 28/45, 5/18, 1/15, 23/30],
[59/90, 1/3, 4/5, 1/10, 11/45, 53/90],
[2/3, 29/90, 11/18, 13/45, 1/15, 23/30],
[2/3, 29/90, 4/5, 1/10, 23/90, 26/45],
[2/3, 37/90, 8/15, 11/30, 1/18, 16/45],
[2/3, 37/90, 3/5, 3/10, 11/90, 13/45],
[2/3, 41/90, 7/15, 11/30, 7/90, 17/45],
[2/3, 41/90, 17/30, 4/15, 8/45, 5/18],
[2/3, 47/90, 2/5, 3/10, 31/90, 8/45],
[2/3, 47/90, 13/30, 4/15, 14/45, 19/90],
[2/3, 59/90, 17/45, 5/18, 7/30, 1/15],
[2/3, 59/90, 37/90, 11/45, 1/5, 1/10],
[61/90, 23/45, 2/5, 3/10, 1/3, 17/90],
[61/90, 23/45, 19/45, 5/18, 14/45, 19/90],
[31/45, 19/90, 47/90, 1/3, 4/15, 17/30],
[31/45, 19/90, 26/45, 5/18, 29/90, 23/45],
[31/45, 7/18, 8/15, 11/30, 7/90, 1/3],
[31/45, 7/18, 26/45, 29/90, 11/90, 13/45],
[32/45, 37/90, 7/15, 11/30, 11/90, 1/3],
[32/45, 37/90, 47/90, 14/45, 8/45, 5/18],
[32/45, 11/18, 1/3, 29/90, 7/30, 1/15],
[32/45, 11/18, 37/90, 11/45, 7/45, 13/90],
[67/90, 26/45, 1/3, 29/90, 1/5, 1/10],
[67/90, 26/45, 17/45, 5/18, 7/45, 13/90],
[37/45, 5/18, 41/90, 1/3, 4/15, 13/30],
[37/45, 5/18, 43/90, 14/45, 13/45, 37/90],
[38/45, 13/90, 11/18, 13/45, 11/45, 53/90],
[38/45, 13/90, 28/45, 5/18, 23/90, 26/45],
[79/90, 13/45, 37/90, 1/3, 3/10, 2/5],
[79/90, 13/45, 19/45, 29/90, 14/45, 7/18],
[9/20, 9/20, 21/40, 37/120, 29/120, 13/24],
[9/20, 9/20, 21/40, 37/120, 13/24, 29/120],
[59/120, 59/120, 11/24, 53/120, 1/15, 23/30],
[59/120, 59/120, 11/24, 53/120, 23/30, 1/15],
[59/120, 59/120, 4/5, 1/10, 49/120, 17/40],
[59/120, 59/120, 4/5, 1/10, 17/40, 49/120],
[61/120, 59/120, 13/24, 53/120, 7/30, 1/15],
[61/120, 59/120, 23/40, 49/120, 1/5, 1/10],
[11/20, 9/20, 19/40, 37/120, 11/24, 29/120],
[11/20, 9/20, 23/40, 31/120, 23/120, 59/120],
[11/20, 9/20, 23/40, 49/120, 19/120, 17/120],
[11/20, 9/20, 19/24, 11/120, 43/120, 19/40],
[11/20, 11/20, 61/120, 23/120, 31/120, 17/40],
[11/20, 11/20, 61/120, 23/120, 17/40, 31/120],
[11/20, 11/20, 21/40, 43/120, 11/120, 5/24],
[11/20, 11/20, 21/40, 43/120, 5/24, 11/120],
[67/120, 41/120, 5/12, 5/12, 29/120, 13/24],
[67/120, 41/120, 5/12, 5/12, 13/24, 29/120],
[67/120, 41/120, 17/30, 4/15, 47/120, 47/120],
[67/120, 53/120, 59/120, 47/120, 1/15, 23/30],
[67/120, 53/120, 19/24, 11/120, 11/30, 7/15],
[7/12, 5/12, 53/120, 41/120, 11/24, 29/120],
[7/12, 5/12, 13/24, 43/120, 7/120, 91/120],
[7/12, 5/12, 13/24, 53/120, 19/120, 17/120],
[7/12, 5/12, 77/120, 31/120, 19/120, 11/24],
[7/12, 7/12, 11/24, 43/120, 7/120, 29/120],
[7/12, 7/12, 11/24, 43/120, 29/120, 7/120],
[7/12, 7/12, 13/24, 19/120, 31/120, 43/120],
[7/12, 7/12, 13/24, 19/120, 43/120, 31/120],
[71/120, 49/120, 8/15, 11/30, 7/120, 91/120],
[71/120, 49/120, 4/5, 1/10, 13/40, 59/120],
[3/5, 3/10, 21/40, 37/120, 47/120, 47/120],
[73/120, 47/120, 53/120, 41/120, 13/30, 4/15],
[73/120, 47/120, 19/40, 37/120, 2/5, 3/10],
[73/120, 59/120, 53/120, 53/120, 1/15, 7/30],
[73/120, 59/120, 53/120, 53/120, 7/30, 1/15],
[73/120, 59/120, 21/40, 43/120, 3/20, 3/20],
[19/30, 7/15, 53/120, 53/120, 11/120, 5/24],
[19/30, 7/15, 53/120, 53/120, 5/24, 11/120],
[19/30, 7/15, 61/120, 23/120, 41/120, 41/120],
[19/30, 8/15, 49/120, 49/120, 7/120, 29/120],
[19/30, 8/15, 49/120, 49/120, 29/120, 7/120],
[19/30, 8/15, 13/24, 19/120, 37/120, 37/120],
[77/120, 43/120, 3/5, 3/10, 7/120, 31/40],
[77/120, 43/120, 97/120, 11/120, 4/15, 17/30],
[77/120, 77/120, 2/5, 3/10, 7/120, 9/40],
[77/120, 77/120, 2/5, 3/10, 9/40, 7/120],
[77/120, 77/120, 13/30, 4/15, 11/120, 23/120],
[77/120, 77/120, 13/30, 4/15, 23/120, 11/120],
[13/20, 7/20, 23/40, 31/120, 7/24, 47/120],
[13/20, 7/20, 71/120, 37/120, 7/120, 31/40],
[13/20, 7/20, 77/120, 31/120, 9/40, 47/120],
[13/20, 7/20, 97/120, 11/120, 11/40, 67/120],
[79/120, 41/120, 7/15, 11/30, 23/120, 59/120],
[79/120, 41/120, 17/30, 4/15, 7/24, 47/120],
[27/40, 59/120, 49/120, 49/120, 1/10, 1/5],
[27/40, 59/120, 49/120, 49/120, 1/5, 1/10],
[27/40, 59/120, 11/24, 43/120, 3/20, 3/20],
[83/120, 37/120, 8/15, 11/30, 19/120, 11/24],
[83/120, 37/120, 3/5, 3/10, 9/40, 47/120],
[83/120, 71/120, 7/20, 7/20, 7/120, 9/40],
[83/120, 71/120, 7/20, 7/20, 9/40, 7/120],
[83/120, 71/120, 13/30, 4/15, 17/120, 17/120],
[17/24, 47/120, 7/20, 7/20, 31/120, 17/40],
[17/24, 47/120, 7/20, 7/20, 17/40, 31/120],
[17/24, 47/120, 13/30, 4/15, 41/120, 41/120],
[29/40, 67/120, 7/20, 7/20, 11/120, 23/120],
[29/40, 67/120, 7/20, 7/20, 23/120, 11/120],
[29/40, 67/120, 2/5, 3/10, 17/120, 17/120],
[89/120, 31/120, 17/24, 23/120, 1/15, 23/30],
[89/120, 31/120, 4/5, 1/10, 19/120, 27/40],
[89/120, 89/120, 7/24, 23/120, 1/15, 7/30],
[89/120, 89/120, 7/24, 23/120, 7/30, 1/15],
[89/120, 89/120, 13/40, 19/120, 1/10, 1/5],
[89/120, 89/120, 13/40, 19/120, 1/5, 1/10],
[91/120, 29/120, 83/120, 5/24, 1/15, 23/30],
[91/120, 29/120, 4/5, 1/10, 7/40, 79/120],
[31/40, 47/120, 7/20, 7/20, 31/120, 43/120],
[31/40, 47/120, 7/20, 7/20, 43/120, 31/120],
[31/40, 47/120, 2/5, 3/10, 37/120, 37/120],
[19/24, 83/120, 29/120, 29/120, 1/15, 7/30],
[19/24, 83/120, 29/120, 29/120, 7/30, 1/15],
[19/24, 83/120, 13/40, 19/120, 3/20, 3/20],
[33/40, 79/120, 29/120, 29/120, 1/10, 1/5],
[33/40, 79/120, 29/120, 29/120, 1/5, 1/10],
[33/40, 79/120, 7/24, 23/120, 3/20, 3/20],
[101/120, 17/120, 9/20, 9/20, 49/120, 17/40],
[101/120, 17/120, 9/20, 9/20, 17/40, 49/120],
[101/120, 17/120, 11/24, 53/120, 5/12, 5/12],
[17/20, 3/20, 59/120, 47/120, 43/120, 19/40],
[17/20, 3/20, 13/24, 43/120, 13/40, 59/120],
[17/20, 3/20, 83/120, 5/24, 19/120, 27/40],
[17/20, 3/20, 17/24, 23/120, 7/40, 79/120],
[103/120, 17/120, 71/120, 37/120, 4/15, 17/30],
[103/120, 17/120, 3/5, 3/10, 11/40, 67/120],
[109/210, 47/105, 39/70, 12/35, 29/210, 53/105],
[109/210, 47/105, 19/30, 4/15, 3/14, 3/7],
[58/105, 109/210, 31/70, 12/35, 52/105, 29/210],
[58/105, 109/210, 4/7, 3/14, 11/30, 4/15],
[41/70, 17/35, 43/105, 79/210, 52/105, 29/210],
[41/70, 17/35, 4/7, 3/14, 1/3, 3/10],
[62/105, 79/210, 17/35, 29/70, 29/210, 53/105],
[62/105, 79/210, 19/30, 4/15, 2/7, 5/14],
[137/210, 44/105, 4/7, 3/14, 2/15, 17/30],
[137/210, 44/105, 64/105, 37/210, 6/35, 37/70],
[137/210, 61/105, 3/7, 3/14, 2/15, 13/30],
[137/210, 61/105, 33/70, 6/35, 37/210, 41/105],
[139/210, 32/105, 68/105, 59/210, 2/35, 59/70],
[139/210, 32/105, 6/7, 1/14, 4/15, 19/30],
[2/3, 3/10, 17/35, 29/70, 3/14, 3/7],
[2/3, 3/10, 39/70, 12/35, 2/7, 5/14],
[2/3, 3/10, 9/14, 2/7, 2/35, 59/70],
[2/3, 3/10, 6/7, 1/14, 19/70, 22/35],
[24/35, 27/70, 4/7, 3/14, 1/10, 2/3],
[24/35, 27/70, 71/105, 23/210, 43/210, 59/105],
[24/35, 43/70, 3/7, 3/14, 1/10, 1/3],
[24/35, 43/70, 46/105, 43/210, 23/210, 34/105],
[73/105, 139/210, 37/105, 59/210, 11/70, 2/35],
[73/105, 139/210, 11/30, 4/15, 1/7, 1/14],
[5/7, 5/14, 43/105, 79/210, 11/30, 4/15],
[5/7, 5/14, 31/70, 12/35, 1/3, 3/10],
[5/7, 5/14, 107/210, 29/105, 2/15, 17/30],
[5/7, 5/14, 19/35, 17/70, 1/10, 2/3],
[5/7, 5/14, 64/105, 37/210, 7/30, 7/15],
[5/7, 5/14, 71/105, 23/210, 7/30, 8/15],
[5/7, 9/14, 1/3, 3/10, 11/70, 2/35],
[5/7, 9/14, 11/30, 4/15, 13/105, 19/210],
[76/105, 107/210, 5/14, 2/7, 2/15, 13/30],
[76/105, 107/210, 33/70, 6/35, 26/105, 67/210],
[51/70, 22/35, 1/3, 3/10, 1/7, 1/14],
[51/70, 22/35, 37/105, 59/210, 13/105, 19/210],
[79/105, 67/210, 107/210, 29/105, 6/35, 37/70],
[79/105, 67/210, 4/7, 3/14, 7/30, 7/15],
[53/70, 19/35, 5/14, 2/7, 1/10, 1/3],
[53/70, 19/35, 46/105, 43/210, 19/105, 53/210],
[23/30, 7/15, 5/14, 2/7, 37/210, 41/105],
[23/30, 7/15, 3/7, 3/14, 26/105, 67/210],
[23/30, 8/15, 5/14, 2/7, 23/210, 34/105],
[23/30, 8/15, 3/7, 3/14, 19/105, 53/210],
[86/105, 53/210, 19/35, 17/70, 43/210, 59/105],
[86/105, 53/210, 4/7, 3/14, 7/30, 8/15],
[92/105, 19/210, 9/14, 2/7, 4/15, 19/30],
[92/105, 19/210, 68/105, 59/210, 19/70, 22/35]
];

/* ----------------------------------------------------------------------- */
/* PLANAR 4-TUPLES OF VECTORS */

/* planarAngle6Family is the Angle6Family for 4 vectors in a plane in counterclockwise order, with the sum of the angles from vector 1 to vector 4 being less than pi. */

planarAngle6Family:=[Q6(0,0,0,0,0,0),
                     Q6(1,0,1,0,1,0),
                     Q6(0,0,1,1,1,1),
                     Q6(0,1,0,1,1,0)];

/* ----------------------------------------------------------------------- */
/* B_3 ROOT LATTICE */

/* The B_3 root lattice contains 18 roots.  For each pair {v, -v} of roots, HalfOfB3 contains the one whose first nonzero coordinate is positive, and B3 contains all 18 roots. */

HalfOfB3:=[Vector(QQ,[1,0,0]),
           Vector(QQ,[0,1,0]),
           Vector(QQ,[0,0,1]),
           Vector(QQ,[1,1,0]),
           Vector(QQ,[1,0,1]),
           Vector(QQ,[0,1,1]),
           Vector(QQ,[1,-1,0]),
           Vector(QQ,[1,0,-1]),
           Vector(QQ,[0,1,-1])
];

B3 := HalfOfB3 cat [-v : v in HalfOfB3];

/* B3AngleMatrix is the 9 x 9 matrix of angles between these vectors. */
/* B3Subspace9 is the corresponding subspace. */

B3AngleMatrix := VectorConfigurationToAngleMatrix(HalfOfB3);
B3Subspace9 := AngleMatrixToSubspace(B3AngleMatrix);

/* B3AngleMatrix8 contains representatives for the two orbits of 8 x 8 principal minors of B3AngleMatrix. */
/* B3Subspaces8 is the sequence consisting of the corresponding two subspaces. */

B3AngleMatrix8 := [ MinorMatrix(B3AngleMatrix,{2,3,4,5,6,7,8,9}) , MinorMatrix(B3AngleMatrix,{1,2,3,4,5,6,7,8}) ];
B3Subspaces8 := [ AngleMatrixToSubspace(am) : am in B3AngleMatrix8 ];

/* ----------------------------------------------------------------------- */
/* ICOSIDODECAHEDRON */

phi := (1+Sqrt(5))/2;

/* The icosidodecahedron is a polytope with 30 vertices situated at the midpoints of the edges of an icoasehedron (or dodecahedron).  For each pair of vertices {v,-v}, HalfOfIcosidodecahedron contains the one whose first nonzero coordinate is positive, and Icosidodecahedron contains all 30 vertices. */
/* IdAngleMatrix is the 15 x 15 AngleMatrix giving the angles between these 15 vectors in R^3. */
/* IdSubspace is the corresponding subspace of ATVs. */

HalfOfIcosidodecahedron:=
[
  Vector(RR,[phi,0,0]),
  Vector(RR,[0,phi,0]),
  Vector(RR,[0,0,phi]),
  0.5*Vector(RR,[1,phi,phi^2]),
  0.5*Vector(RR,[phi^2,1,phi]),
  0.5*Vector(RR,[phi,phi^2,1]),
  0.5*Vector(RR,[1,phi,-phi^2]),
  0.5*Vector(RR,[phi^2,1,-phi]),
  0.5*Vector(RR,[phi,phi^2,-1]),
  0.5*Vector(RR,[1,-phi,phi^2]),
  0.5*Vector(RR,[phi^2,-1,phi]),
  0.5*Vector(RR,[phi,-phi^2,1]),
  0.5*Vector(RR,[1,-phi,-phi^2]),
  0.5*Vector(RR,[phi^2,-1,-phi]),
  0.5*Vector(RR,[phi,-phi^2,-1])
];

Icosidodecahedron := HalfOfIcosidodecahedron cat [-v : v in HalfOfIcosidodecahedron];

IdAngleMatrix := VectorConfigurationToAngleMatrix(HalfOfIcosidodecahedron);
IdSubspace := AngleMatrixToSubspace(IdAngleMatrix);

/* IsIcosidodecahedronEdge(pair) takes a 2-element subset of {1,...,30} and returns True if the angle between the corresponding icosidodecahedron vertices is pi/5. */

function IsIcosidodecahedronEdge(pair);
   seq := Icosidodecahedron[SetToSequence(pair)];
   return IsApproximatelyZero(CosineOfAngleBetween(seq[1],seq[2])-Cos(pi/5));
end function;

IcosidodecahedronEdges := { pair : pair in Subsets({1..30},2) | IsIcosidodecahedronEdge(pair) };

IcosidodecahedronTriangles := { threes : threes in Subsets({1..30},3) | Subsets(threes,2) subset IcosidodecahedronEdges };


/* ----------------------------------------------------------------------- */

sporadicTetrahedraSubspaces := ATVSymmetricGroupNegationsRepresentatives(4,[ RubinsteinToSubspace(rub): rub in sporadicTetrahedra ]);

HillSubspaces:=ATVSymmetricGroupNegationsRepresentatives(4,[Dihedral6FamilyToSubspace(df): df in HillDihedral6Families]);

RubinsteinDihedral6Families2 := [[Vector(QQ,seq3[1]), Vector(QQ,seq3[2]), Vector(QQ,seq3[3])] : seq3 in RubinsteinDihedral6Families2Raw];
RubinsteinSubspaces2Redundant := [ Dihedral6FamilyToSubspace(df) : df in RubinsteinDihedral6Families2 ];
RubinsteinSubspaces2 := ATVSymmetricGroupNegationsRepresentatives(4,RubinsteinSubspaces2Redundant);
allRubinsteinSubspaces2 := ExpandedList(ExplicitSymmetricGroupNegations[4],RubinsteinSubspaces2);

RubinsteinDihedral6Families1 := [[Vector(QQ,seq2[1]), Vector(QQ,seq2[2])] : seq2 in RubinsteinDihedral6Families1Raw];
RubinsteinSubspaces1Redundant := [ Dihedral6FamilyToSubspace(df) : df in RubinsteinDihedral6Families1 ];
RubinsteinSubspaces1 := SequenceDiff( ATVSymmetricGroupNegationsRepresentatives(4,RubinsteinSubspaces1Redundant) , HillSubspaces);
allRubinsteinSubspaces1 := ExpandedList(ExplicitSymmetricGroupNegations[4],RubinsteinSubspaces1);

RubinsteinDihedral6s0 := [Vector(QQ,seq1) : seq1 in RubinsteinDihedral6s0Raw];
RubinsteinSubspaces0Redundant := [ Dihedral6ToSubspace(dih) : dih in RubinsteinDihedral6s0 ];
RubinsteinSubspaces0 := ATVSymmetricGroupNegationsRepresentatives(4,RubinsteinSubspaces0Redundant);
allRubinsteinSubspaces0 := ExpandedList(ExplicitSymmetricGroupNegations[4],RubinsteinSubspaces0);

KedlayaSubspacesInitial := [ Dihedral6FamilyToSubspace(ked) : ked in KedlayaDihedral6FamiliesFixed ];
KedlayaSubspaces := ATVSymmetricGroupNegationsRepresentatives(4,KedlayaSubspacesInitial);
KedlayaDihedral6FamilyRepresentatives:= [AdjustDihedral6Range(SubspaceToDihedral6Family(sub)) : sub in KedlayaSubspaces];

KedlayaSubspaces2Initial := [ Dihedral6FamilyToSubspace(ked) : ked in KedlayaDihedral6Families2 ];
KedlayaSubspaces2 := ATVSymmetricGroupNegationsRepresentatives(4,KedlayaSubspaces2Initial);

perpSubspaceUnnormalized := Dihedral6FamilyToSubspace(perpDihedral6Family);
perpSubspace := ATVSymmetricGroupNegationsRepresentative(4,perpSubspaceUnnormalized);

planarSubspace := SubspaceOrbitRepresentative(ExplicitSymmetricGroupNegations[4],Angle6FamilyToSubspace(planarAngle6Family));

stupidSubspaces := [perpSubspace,planarSubspace];

/* subspaceUniverse is the universe containing subspaces of arbitrary dimension.   This has a technical use, for initializing an empty sequence, so that Magma knows what kind of elements it will have. */

subspaceUniverse:=Universe(HillSubspaces cat stupidSubspaces);


/* ----------------------------------------------------------------------- */

/* ContainingFamily(sub), where sub is a subspace parametrizing ATVs corresponding to 4-vector configurations, returns the subspace that is the S_4 x {+-1} representative of a maximal family (one with the most parameters) that contains some S_4 x {+-1} transform of sub. */

function ContainingFamily(sub)
   rep := SubspaceOrbitRepresentative(ExplicitSymmetricGroupNegations[4],sub);
   if IsSubfamily(4,rep,planarSubspace) then return planarSubspace; end if;
   if IsSubfamily(4,rep,perpSubspace) then return perpSubspace; end if;
   for i in [1..#RubinsteinSubspaces2] do
      if IsSubfamily(4,rep,RubinsteinSubspaces2[i]) then return RubinsteinSubspaces2[i]; end if;
   end for;
   for i in [1..#RubinsteinSubspaces1] do
      if IsSubfamily(4,rep,RubinsteinSubspaces1[i]) then return RubinsteinSubspaces1[i]; end if;
   end for;
   for i in [1..#HillSubspaces] do
      if IsSubfamily(4,rep,HillSubspaces[i]) then return HillSubspaces[i]; end if;
   end for;
   for i in [1..#sporadicTetrahedraSubspaces] do
      if rep eq sporadicTetrahedraSubspaces[i] then return sporadicTetrahedraSubspaces[i]; end if;
   end for;
   for i in [1..#RubinsteinSubspaces0] do
      if rep eq RubinsteinSubspaces0[i] then return RubinsteinSubspaces0[i]; end if;
   end for;
   print "The subspace does not belong to any family!";
   assert false; /* If one reaches this point, then the subspace does not belong to any family!  This should not happen. */
end function;

/* FamilyName(sub), where sub is a subspace parametrizing ATVs corresponding to 4-vector configurations, returns a string containing the name of the family it represents.  If it is not equal to one of the named families, then the function is applied to the family containing an S_4 x {+-1}^4 conjugate of sub, if such a family exists. */

function FamilyName(sub)
   if sub eq planarSubspace then return Sprintf("Planar 3-parameter family"); end if;
   if sub eq perpSubspace then return Sprintf("Perpendicular 2-parameter family"); end if;
   for i in [1..#RubinsteinSubspaces2] do
       if sub eq RubinsteinSubspaces2[i] then return Sprintf("Rubinstein 2-parameter family \%o",i); end if;
   end for;
   for i in [1..#RubinsteinSubspaces1] do
       if sub eq RubinsteinSubspaces1[i] then return Sprintf("Rubinstein 1-parameter family \%o",i); end if;
   end for;
   for i in [1..#HillSubspaces] do
       if sub eq HillSubspaces[i] then return Sprintf("Hill 1-parameter family \%o",i); end if;
   end for;
   for i in [1..#sporadicTetrahedraSubspaces] do
       if sub eq sporadicTetrahedraSubspaces[i] then return Sprintf("Sporadic tetrahedron \%o",i); end if;
   end for;
   for i in [1..#RubinsteinSubspaces0] do
       if sub eq RubinsteinSubspaces0[i] then return Sprintf("Rubinstein degenerate \%o",i); end if;
   end for;
   rep := ContainingFamily(sub);
   if rep eq sub 
      then print "The subspace has no name!"; 
           return "Unknown family";
   else return FamilyName(rep);
   end if;
end function;

/* MinorNames(bigsub), where bigsub is a subspace parametrizing ATVs corresponding to n x n AngleMatrices, returns the sequence of family names corresponding to the principal 4 x 4 minors.  A second output is the list of 4-element subsets of {1,2,...,n} in the order used. */

/* printMinorNames(bigsub) is similar, but is a procedure that prints out each subset and the family name of the corresponding minor. */

function MinorNames(bigsub)
   n := nOfSubspace(bigsub);
   output1 := [];
   output2 := [];
   for I in Subsets({1..n},4) do
      Append(~output1,FamilyName(MinorSubspace(bigsub,I)));
      Append(~output2,I);
   end for;
   return output1, output2;
end function;

procedure printMinorNames(bigsub)
   n := nOfSubspace(bigsub);
   for I in Subsets({1..n},4) do
      printf "%o minor is %o\n",I,FamilyName(MinorSubspace(bigsub,I));
   end for;
end procedure;


/* SymmetryGroup(sub) takes a subspace sub of ATVs corresponding to n x n AngleMatrices, and returns the subgroup of S_n semidirect ({+-1}^n /diagonal{+-1}) that preserves it. */

function SymmetryGroup(sub)
   mat:=SubspaceToAngleMatrixFamily(sub)[1];
   n:=Ncols(mat);
   return Stabilizer(ExplicitSymmetricGroupNegations[n],sub);
end function;

/* SymmetryGroupOfSpecialization(sub) takes sub and returns the SymmetryGroup of a typical member of the family, i.e., of a typical 1-dimensional subspace.  The specialization is not guaranteed to be generic enough. */

function SymmetryGroupOfSpecialization(sub)
   return SymmetryGroup(Specialization(sub));
end function;

/* ----------------------------------------------------------------------- */
/* DATABASE-PRODUCING ROUTINES

/* IntersectWithOneMore(subspacelist,sub) intersects each subspace in subspacelist with sub, discards the ones that correspond to an empty affine space, and returns the sequence of remaining intersections. */

function IntersectWithOneMore(n,subspacelist,sub)
   output:=[subspaceUniverse|];
   for subspace in subspacelist do
      intersection:=subspace meet sub;
      if IsReasonable(intersection)
/*         then Append(~output,SubspaceOrbitRepresentative(ExplicitNegationGroups[n],intersection)); */
           then 
                otherintersection:=intersection*ExplicitLastNegation[n];
                code1:=Eltseq(EchelonMatrix(intersection));
                code2:=Eltseq(EchelonMatrix(otherintersection));
                Append(~output, code1 le code2 select intersection else otherintersection);
      end if;
   end for;
   return output;
end function;

/* IntersectWithAll(subspacelist,subs) concatenates the output of IntersectWithOneMore(subspacelist,sub) as sub ranges over all possible subspaces in subs.  For each subspace in the output, if it corresponds to a 1-parameter family, the interval I of allowable parameter values is computed; if I is only a point, then the 1-parameter family becomes a 0-parameter family whose angles are checked to be in (0,pi) before including it; if I is empty, the family is discarded.  */

function IntersectWithAll(n,subspacelist,subs)
   output:=[subspaceUniverse|];
   for sub in subs do
      output cat:= IntersectWithOneMore(n,subspacelist,sub);
   end for;
   output := EliminateDuplicates(output);
   newoutput := [subspaceUniverse|];
   for sub in output do
      if Dimension(sub)-1 eq 1 then 
         interval := SubspaceInterval(sub);
         c := interval[1];  
         d := interval[2];
         if c lt d then Append(~newoutput,sub);
/*         elif c gt d then print SubspaceToParametrizedAngleMatrix(sub); print interval;       */
         elif c eq d then 
            newsub := SpecializeSubspace(sub,Vector(QQ,[c]));
   	                      Append(~newoutput,newsub);
            if IsReasonable(newsub) then Append(~newoutput,newsub); end if; 
         end if;
      else Append(~newoutput,sub);
      end if;
   end for;
   return EliminateDuplicates(newoutput);
end function;

/* NextList(n,initialsubspaces,allowablesubspaces), where n >= 5, initialsubspaces is a sequence of subspaces parametrizing ATVs corresponding to (n-1) x (n-1) matrices, and allowablesubspaces is a sequence of subspaces parametrizing ATVs corresponding to 4 x 4 matrices, returns the sequence of subspaces parametrizing ATVs corresponding to n x n matrices extending an (n-1) x (n-1) matrix in initialsubspaces each of whose 4 x 4 principal minors corresponds to a subspace in the S_4 semidirect {+-1}^4 orbit a subspace in allowablesubspaces.  There is an action of the signed permutation group S_n semidirect {+-1}^n on the set of such subspaces, so actually only one representative from each orbit is returned. */

function NextList(n,initialsubspaces,allowablesubspaces)
   assert n ge 5;
   proj := RemoveRowColumnLinearTransformation(n,n);
   output := [subspaceUniverse | InverseImageSubspace(proj,sub) : sub in initialsubspaces];
/*   fours:=[S : S in Subsets({1..n},4) | n in S]; */
   fours := Subsets4[n];
   for S in fours do
      printf "CPU time: %o  Merging with %o minor: ", Cputime(),S;
      projS := MinorMatrixLinearTransformation(n,S);
      Sallsubs := [InverseImageSubspace(projS,sub) : sub in allowablesubspaces];
      output := IntersectWithAll(n,output,Sallsubs);
      printf "%o subspaces\n", #output;
   end for;
   printf "CPU time: %o  Computing orbit representatives...\n", Cputime();
   outputreps := ATVSymmetricGroupNegationsRepresentatives(n,output);
   printf "CPU time: %o  Before eliminating subconjugates, there are %o subspaces.\n", Cputime(), #outputreps;   /* */
   return EliminateSubconjugates(outputreps);
end function;

/* PreviousList(subspacelist,n), where subspacelist is a sequence of subspaces parametrizing ATVs corresponding to (n+1) x (n+1) matrices, and n >= 4, returns the sequence of subspaces obtained by taking the "forget row i and column i" projection for any i.  There is an action of the signed permutation group S_n semidirect {+-1}^n on the set of such subspaces, so actually only one representative from each orbit is returned. */

function PreviousList(n,subspacelist)
   assert n ge 4;
   output:=[];
   for i in [1..n+1] do
       proj:=RemoveRowColumnLinearTransformation(n+1,i);
       output cat:= [sub*proj : sub in subspacelist];
   end for;
   return EliminateSubconjugates(ATVSymmetricGroupNegationsRepresentatives(n,output));
end function;

/* ProcessList(n,initialsubspaces,allowablesubspacerepresentatives) where n >= 4, initialsubspaces is a sequence of subspaces parametrizing ATVs corresponding to n x n matrices, and allowablesubspacerepresentatives is a sequence of subspaces parametrizing ATVs corresponding to 4 x 4 matrices, fills database[m] with a sequence of subspaces parametrizing ATVs corresponding to m x m matrices having a principal n x n minor in initialsubspaces and whose 4 x 4 minors outside that n x n minor are all in the S_4 semidirect {+-1}^4 orbit of allowablesubspacerepresentatives.  It returns that database. */

function ProcessList(n,initialsubspaces,allowablesubspacerepresentatives)
   assert n ge 4;
   database:=[[subspaceUniverse|]: i in [1..maxsize]];
   database[n]:=initialsubspaces;
   allowablesubspaces:=ExpandedList(ExplicitSymmetricGroupNegations[4],allowablesubspacerepresentatives);
   m:=n;
   while m lt maxsize and not IsEmpty(database[m]) do
      m+:=1;
      printf "Currently forming %o-vector configurations...\n", m;
      database[m]:=NextList(m,database[m-1],allowablesubspaces);
      printf "\ndatabase[%o] has %o parametrized angle matrices:\n", m, #database[m];
      print [SubspaceToParametrizedMatrix(sub): sub in database[m]], "\n\n";
   end while;
   return database;
end function;

/* NewList(n,database), where n >= 4 and database is an output from ProcessList, returns database[n] - PreviousList(n,database[n+1]).  That is, it returns the sequence of subspaces corresponding to n x n matrices that do not come from subspaces corresponding to (n+1) x (n+1) matrices. */

function NewList(n,database)
   assert n ge 4;
   return SequenceDiff( database[n] , PreviousList(n,database[n+1]));
end function;

/* NewListAfterRegge(database), where database is an output from ProcessList, returns Regge orbit representatives of subspaces in database[4] that are not Regge equivalent to subspaces coming from database[5]. */

function NewListAfterRegge(database)
   return SequenceDiff( ReggeRepresentatives(database[4]) , ReggeRepresentatives(PreviousList(4,database[5]) cat stupidSubspaces));
end function;


/* MakeNew(database) returns a new database consisting of those n-vector configuration subspaces that do not extend to (n+1)-vector configuration subspaces in the database. */

function MakeNew(database)
   newdatabase := [[subspaceUniverse|]: i in [1..maxsize]];
   for n in [4..maxsize-1] do
      newdatabase[n]:=NewList(n,database);
   end for;
   return newdatabase;
end function;

/* AddSubconfigurations(database) adds to database all the subconfigurations of all the configurations in database. */

function AddSubconfigurations(database) 
   newdatabase := database;
   for n in Reverse([4..maxsize-1]) do
       newdatabase[n] := EliminateDuplicates(newdatabase[n] cat PreviousList(n,newdatabase[n+1]));
   end for;
   return newdatabase;
end function;

/* SubspacesToDatabase(seq), takes a sequence of subspaces, possibly corresponding to n-vector configuration families for different values of n, and organizes them into a list of length maxsize whose n-th term is the sequence of subspaces for that n. */
/* SubspaceToDatabase(sub) is the same for one subspace - it just places it in the n-th sequence, for the right value of n, and the m-th sequence will be empty for m not equal to n  */

/* SubspacesToSubconfigurationDatabase(subs) is similar, but it include all subconfiguration families in the database. */
/* SubspaceToSubconfigurationDatabase(sub) is similar, but it include all subconfiguration families in the database. */

function SubspacesToDatabase(subs) 
   newdatabase := [[subspaceUniverse|]: i in [1..maxsize]];
   for sub in subs do
       n:=nOfSubspace(sub);
       newdatabase[n] cat:= [sub];
   end for;
   return newdatabase;
end function;

function SubspaceToDatabase(sub)
   return SubspacesToDatabase([sub]);
end function;

function SubspacesToSubconfigurationDatabase(subs)
   return AddSubconfigurations(SubspacesToDatabase(subs));
end function;

function SubspaceToSubconfigurationDatabase(sub)
   return AddSubconfigurations(SubspaceToDatabase(sub));
end function;


/* DatabaseOfmParameterFamilies(db,m) takes a database of subspaces, and returns the possibly smaller database whose n-th term is the subsequence of subspaces corresponding to AngleMatrix families with exactly m parameters. */
function DatabaseOfmParameterFamilies(db,m)
   return [ [sub : sub in db[n] | Dimension(sub) eq m+1] : n in [1..maxsize]];   
end function;

/* DisplayDatabase(db), takes a sequence db whose n-th element is a sequence of subspaces corresponding to families of n x n AngleMatrices, and prints these parametrized AngleMatrices for each n. */
/* DisplayDatabase(db,m) is the same except that only the families with exactly m parameters are displayed, where m is a nonnegative integer. */

procedure DisplayDatabase(list,...)
   if #list eq 1 then db := list[1];
      else db:= DatabaseOfmParameterFamilies(list[1],list[2]);
   end if;
   for n in [4..maxsize] do
      if not IsEmpty(db[n]) then
         printf "The number of %o x %o angle matrices is %o, and here they are:\n", n, n, #db[n];
         print [SubspaceToParametrizedMatrix(sub) : sub in db[n]];
         printf "\n";
      end if;
   end for;
   printf "Summary of counts: %o.\n", [#db[n]:n in [1..maxsize]];
end procedure;


/* ----------------------------------------------------------------------- */
/* PRINTING FOR tikZ */

procedure drawLine(a,b);
   printf "\\draw (%.5o,%.5o,%.5o) -- (%.5o,%.5o,%.5o);\n", a[1],a[2],a[3],b[1],b[2],b[3];
end procedure;

procedure drawVector(a);
   drawLine(Vector(QQ,[0,0,0]),a);
   printf "\\draw[fill] (%.5o,%.5o,%.5o) circle [radius=0.1];\n", a[1],a[2],a[3];
end procedure;

procedure drawVectors(seq);
   for pt in seq do
      drawVector(pt);
   end for;
end procedure;

procedure drawTriangle(seq);
   assert #seq eq 3;
   a := seq[1];
   b := seq[2];
   c := seq[3];
   printf "\\filldraw[fill=red!20!white, draw=black, fill opacity=0.5] (%.5o,%.5o,%.5o) -- (%.5o,%.5o,%.5o) -- (%.5o,%.5o,%.5o) -- (%.5o,%.5o,%.5o);\n", a[1],a[2],a[3], b[1],b[2],b[3], c[1],c[2],c[3], a[1],a[2],a[3];
end procedure;

procedure drawIcosidodecahedronTriangles();
   for tri in IcosidodecahedronTriangles do
      drawTriangle(Icosidodecahedron[SetToSequence(tri)]);
   end for;
end procedure;

/* ----------------------------------------------------------------------- */
/* PRINTING FOR LATEX */

/* PrintLinearForm(a,b) prints a+bx in LaTeX form. */

procedure PrintLinearForm(a,b) 
   if a eq 0 then 
      if b eq 0 then printf "0";
      elif b eq 1 then printf "x";   
      elif b eq -1 then printf " -x";
      elif b gt 0 then printf " %o x", b;
      elif b lt 0 then printf " -%o x", Abs(b);
      end if;
   else 
      printf "%o", a;
      if b eq 1 then printf " + x";
      elif b eq -1 then printf " - x";
      elif b gt 0 then printf " + %o x", b;
      elif b lt 0 then printf " - %o x", Abs(b);
      end if;
   end if;
end procedure;

/* PrintAngleMatrix(am) takes an AngleMatrix of constants, and prints it in LaTeX. */

procedure PrintAngleMatrix(am)
   size:=Nrows(am);
   printf "$\\begin{pmatrix}\n";
   for i in [1..size] do
      for j in [1..size] do
         printf "%o", am[i,j];
         if j eq size then
             printf " \\\\\n";  /* This is \\ followed by a newline. */
         else printf " & ";
         end if;
      end for;
   end for;
   printf "\\end{pmatrix}$\n";
end procedure;

/* Print1ParameterFamily(sub) takes a subspace corresponding to a 1-parameter family of ATVs, and prints LaTeX code producing a corresponding parameterized angle matrix with parameter x, adjusted so that its range is [0,q] for some rational number q.  It also prints the range. */

procedure Print1ParameterFamily(sub)
   assert Dimension(sub) eq 2;
   amf:=SubspaceToAngleMatrixFamily(sub);
   adjustedamf,q:=AdjustAngleMatrixFamily(amf);
   constantcoeffs:=adjustedamf[1];
   linearcoeffs:=adjustedamf[2];
   size:=Nrows(constantcoeffs);
   printf "$\\begin{pmatrix}\n";
   for i in [1..size] do
      for j in [1..size] do
         PrintLinearForm(constantcoeffs[i,j],linearcoeffs[i,j]);
         if j eq size then
             printf " \\\\\n";  /* This is \\ followed by a newline. */
         else printf " & ";
         end if;
      end for;
   end for;
   printf "\\end{pmatrix}\n";
   printf "\\textup{ for } 0 \\le x \\le %o $,\n", q;
end procedure;

/* Print5AndUp(db) prints S_n+- representatives of the maximal n-vector configurations in database db for n >= 5 in reverse order, in LaTeX form.  It breaks the line after each 1-parameter family, and after every other isolated example, and after the last isolated example of each size, and after any example that is 8 x 8 or larger. */

procedure Print5AndUp(db)
   db0:=DatabaseOfmParameterFamilies(db,0);
   db1:=DatabaseOfmParameterFamilies(db,1);
   for n := maxsize to 5 by -1 do
      for sub in db1[n] do
         Print1ParameterFamily(sub);
         printf " \\\\\n";
      end for;
      for i in [1..#db0[n]] do
         PrintAngleMatrix(SubspaceToAngleMatrix(db0[n][i]));
         if IsEven(i) or i eq #db0[n] or n ge 8 then printf " \\\\\n"; end if;
	 if i eq #db0[n] and n ne 5 then printf "\\hrule\n"; end if;
      end for;
   end for;
end procedure;

/* Print4(ams) takes a sequence of 4 x 4 AngleMatrices and prints them in LaTeX form, 3 to a line. */

procedure Print4(ams)
   for i in [1..#ams] do
      PrintAngleMatrix(ams[i]);
      if i mod 3 eq 0 then printf " \\\\\n"; end if;
   end for;
end procedure;



/* ----------------------------------------------------------------------- */
/* SUBSPACE LISTS */

/* tetrahedraSubspaces contains the S_4 semidirect {+-1}^4 representatives of all the subspaces corresponding to nondegenerate tetrahedra, whether isolated or 1-parameter families. */
/* RubinsteinSubspaces contains the same for minimally degenerate tetrahedra not in the perpSubspace or planarSubspace families. */
/* representativeSubspaces contains all of the above, including perpSubspace and planarSubspace. */

tetrahedraSubspaces := sporadicTetrahedraSubspaces cat HillSubspaces;
RubinsteinSubspaces := RubinsteinSubspaces0 cat RubinsteinSubspaces1 cat RubinsteinSubspaces2;
representativeSubspaces := tetrahedraSubspaces cat RubinsteinSubspaces cat stupidSubspaces;

/* IdSubspaces4 consists of the orbit representatives of the subspaces corresponding to 4 x 4 principal minors of IdAngleMatrix. */
/* IdSubspaces4Families returns the maximal families containing those. */
/* IdSubspaces4FamiliesNonstupid is the same, with perpSubspace and planarSubspace removed.  Actually, perpSubspace was not in there to begin with, so only planarSubspace is removed. */

IdSubspaces4 := ATVSymmetricGroupNegationsRepresentatives(4,MinorSubspaces(IdSubspace,4));
IdSubspaces4Nonstupid := [sub : sub in IdSubspaces4 | IsReasonable(sub)];
IdSubspaces4Families := EliminateDuplicates([ContainingFamily(sub) : sub in IdSubspaces4]);
IdSubspaces4FamiliesNonstupid := SequenceDiff(IdSubspaces4Families,stupidSubspaces);

/* inputSubspaceLists contains a partition of the list of subspaces corresponding to 4 x 4 AngleMatrices, ordered from highest "priority" to lowest.  We later classify n-vector configurations according to the highest priority 4-vector configuration they contain. */

inputSubspaceLists := 
[ 
   SequenceDiff( sporadicTetrahedraSubspaces , IdSubspaces4FamiliesNonstupid ),
   SequenceDiff( RubinsteinSubspaces0 , IdSubspaces4FamiliesNonstupid ),
   SequenceDiff( HillSubspaces , IdSubspaces4FamiliesNonstupid ),
   SequenceDiff( RubinsteinSubspaces1 , IdSubspaces4FamiliesNonstupid ),
   SequenceDiff( RubinsteinSubspaces2 , IdSubspaces4FamiliesNonstupid ),
   IdSubspaces4FamiliesNonstupid,
   stupidSubspaces
];

function DatabaseStartingWithGroup(m)
   return ProcessList(4, inputSubspaceLists[m], &cat inputSubspaceLists[m..#inputSubspaceLists]);
end function;

/* ----------------------------------------------------------------------- */
/* SOME COMMANDS FOR GENERATING THE DATABASES OF RESULTS */

/* The commands below can be cut and paste into the Magma session.  They are not run automatically upon loading, because some of them take a long time to complete (about 14 hours on on an Intel Xeon CPU E5-1620 v3 @ 3.50GHz).  Each "database" constructed below is a sequence whose n-th term database[n] contains S_n semidirect {+-1}^n orbit representatives for the subspaces corresponding to n-vector configurations.  They are separated according to the "priority" of the initial 4-vector configuration, as defined by inputSubspaceLists above; the advantage of this division is that in looping over possibilities for each other principal 4 x 4 minor, one does not need to consider possibilities of higher priority, so much time is saved. 

   totalDatabase is the union of all the results, excluding those configurations that are planar or that are planar except for one vector perpendicular to all others. 
   newDatabase is the same, except that n-vector configurations contained in n'-vector configurations for some n' > n are omitted.  In other words, newDatabase contains maximal n-vector configurations only. 
   DisplayDatabase(newDatabase) presents this data in a prettier form, as parametrized angle matrices.

   The "Profile" commands use the Magma profiler to see how much time is being used by the various subroutines, after a computation has been done. 

ProfileReset(); 

time sporadicDatabase := DatabaseStartingWithGroup(1);
time Rubinstein0Database := DatabaseStartingWithGroup(2);
time HillDatabase := DatabaseStartingWithGroup(3);
time Rubinstein1Database := DatabaseStartingWithGroup(4);
time Rubinstein2Database := DatabaseStartingWithGroup(5);
time IdDatabase := DatabaseStartingWithGroup(6);

time totalDatabase := [ EliminateSubconjugates(EliminateDuplicates( sporadicDatabase[n] cat Rubinstein0Database[n] cat HillDatabase[n] cat Rubinstein1Database[n] cat Rubinstein2Database[n] cat IdDatabase[n])) : n in [1..maxsize]];
time newDatabase := MakeNew(totalDatabase);
time newSubspaces := &cat newDatabase;
time ReggeNew := NewListAfterRegge(totalDatabase);
time NiceReggeAngleMatrices := [ NiceReggeRepresentative(sub) : sub in ReggeNew ];

DisplayDatabase(newDatabase);

Print5AndUp(newDatabase);

Print4(NiceReggeAngleMatrices);

ProfilePrintByTotalTime(ProfileGraph());

*/
