module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

@[expose] public section

open UpperTheory.GalN.V

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws


variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}


end

section


private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1

private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]

end
