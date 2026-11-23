module

public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.factTypePrime
variable {g : ℕ} [Fact g.Prime]
theorem locType_of_serParamLe_alt {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)
theorem locType_of_labTie_locComp_labParamLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  _root_.DiscreteGroups.sglob.DzType.Rt.locType_of_serParamLe_alt hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from _root_.funext fun n => _root_.funext (hS k n)]
    exact hP k v
end DiscreteGroups.sglob.DzType.Rt
end
end
