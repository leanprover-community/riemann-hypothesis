module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isFullLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsFullLattice E (stdL E n) := by
  letI := isLattice_stdL E n
  refine ⟨?_⟩
  rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2
  funext i
  exact (Pi.basisFun_apply E (Fin n) i).symm

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isFullLattice_stdL D.host.E S.rank) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hΛT)
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
