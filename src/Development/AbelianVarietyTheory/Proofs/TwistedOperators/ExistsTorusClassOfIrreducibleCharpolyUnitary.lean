module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEqStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormClassOfRationalIsometryTraceFormStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryTorusTraceFormOfHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRationalDiagonalHomBijectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RatEll

theorem sig_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

theorem exists_cls_of_irreducible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Function.Bijective (diagH σ J F) ∧ ∀ γ : GRat σ J, Irreducible γ.1.1.charpoly → ∃ P : PPol σ n, γ.1.1.charpoly = P.1 ∧ ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  refine ⟨GlobalTheory.T.unitaryRationalDiagonalHom_bijective F E σ n J, ?_⟩
  intro γ hirr
  have hm : Formalism.UG.cT (σ : E →+* E) γ.1.1 * J * γ.1.1 = J := γ.2
  have hs := GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal F E σ n J hJ.2 γ
  have hdet : γ.1.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero
  have h0 : eval 0 γ.1.1.charpoly ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hc
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
  have hP : γ.1.1.charpoly.Monic ∧ Irreducible γ.1.1.charpoly ∧ γ.1.1.charpoly.natDegree = n ∧
      eval 0 γ.1.1.charpoly ≠ 0 ∧ γ.1.1.charpoly = sharp σ n γ.1.1.charpoly :=
    ⟨Matrix.charpoly_monic _, hirr, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], h0, hs⟩
  let P : PPol σ n := ⟨γ.1.1.charpoly, hP⟩
  refine ⟨P, rfl, ?_⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq F E σ n P γ.1.1 rfl
  obtain ⟨x, hx0, hxs, hxf⟩ := GlobalTheory.T.exists_unitaryTorus_traceForm_of_hermitian F E σ (sig_sig hσ) n P J hJ γ.1.1 hm φ hφ
  exact GlobalTheory.T.exists_normClass_of_rationalIsometry_traceForm F E σ n P J φ x hx0 hxs hxf γ hφ

end GlobalTheory.TrEll.RatEll
