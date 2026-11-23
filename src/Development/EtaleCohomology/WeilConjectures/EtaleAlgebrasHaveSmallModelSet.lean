module

public import Development.EtaleCohomology.WeilConjectures.AbsorbPf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.EWeil.AbsorbPf3

theorem etaleAlgebras_have_small_model_set : LateralTheory.EWeil.AbsorbPf.Model := by
  intro A
  refine ⟨Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) A) // (algebraMap A (MvPolynomial (Fin n) A ⧸ I)).Etale},
    fun x => CommRingCat.of (MvPolynomial (Fin x.1) A ⧸ x.2.1),
    fun x => CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin x.1) A ⧸ x.2.1)), fun x => x.2.2, ?_⟩
  intro B g hg
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hg
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let eq : (MvPolynomial (Fin n) A ⧸ RingHom.ker f) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
  haveI : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := Algebra.Etale.of_equiv eq.symm
  have hE : (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)).Etale :=
    (RingHom.etale_algebraMap).mpr inferInstance
  refine ⟨⟨n, RingHom.ker f, hE⟩, (eq.symm.toRingEquiv).toCommRingCatIso, ?_⟩
  ext a
  exact eq.symm.commutes a

end LateralTheory.EWeil.AbsorbPf3
