module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFamily_trace_volume_const : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  first | exact @GlobalTheory.HL.FamilyVol.family_vol | exact GlobalTheory.HL.FamilyVol.family_vol | (intros; apply GlobalTheory.HL.FamilyVol.family_vol <;> assumption)
