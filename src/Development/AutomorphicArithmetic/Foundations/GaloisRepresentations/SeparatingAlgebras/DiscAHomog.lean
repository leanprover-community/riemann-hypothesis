import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private noncomputable def discA (a n : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ p ∈ (Finset.univ : Finset (Fin a)).offDiag, ∏ c ∈ Finset.Icc 1 n,
    (MvPolynomial.X p.1 ^ c - MvPolynomial.X p.2 ^ c)

private noncomputable def discB (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ q ∈ (Finset.univ : Finset (Fin a × Fin a × Fin a)).filter
      (fun q => ¬ (q.1 = q.2.1 ∧ q.2.2 = q.2.1)),
    (MvPolynomial.X q.1 * MvPolynomial.X q.2.2 - MvPolynomial.X q.2.1 ^ 2)







