module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSymplecticBasisLocalExtension
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

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN

theorem _root_.GlobalTheory.T.hermitian_symplectic_basis_local_extension : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : ∀ i j, sig (Hm j i) = Hm i j) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (hXY : ∀ a b, hq sig Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hq sig Hm (X a) (X b) = 0) (hYY : ∀ a b, hq sig Hm (Y a) (Y b) = 0) (up : ∀ p, Fin N → (A.loc p).Ep) (sp : ∀ p, (A.loc p).Ep) (horth : ∀ p, ∀ a ∈ T, hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (X a)) = 0 ∧ hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (Y a)) = 0) (hs : ∀ p, sp p + (A.L p).cj (sp p) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) (hint : {p | ¬ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O)}.Finite) (d : ∀ p, ((A.loc p).Fp)ˣ) (hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite), ∃ (u : Fin N → E) (s : E), (∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0) ∧ s + sig s = hq sig Hm u u ∧ ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o) ∧ ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o := by
  first | exact @GlobalTheory.HL.EichlerParams.strong_approx_params | exact GlobalTheory.HL.EichlerParams.strong_approx_params | (intros; apply GlobalTheory.HL.EichlerParams.strong_approx_params <;> assumption)
