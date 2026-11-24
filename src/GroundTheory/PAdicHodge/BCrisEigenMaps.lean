module

public import GroundTheory.PAdicHodge.FontaineLemmaInvariants
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section AInfToBCris

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] {p : ℕ} [hp : Fact p.Prime]
  [IsPerfectoidField F p] {ε : PreTilt (normInteger F) p}

/-- The canonical map `AInf F p → BCris hε`.

Stated for a general perfectoid field `F`, not only for `ℂ_[p]`. Over `ℂ_[p]` the ring structure
on `BCris hε` contains instance proofs specialised to `ℂ_[p]`; Lean moves these into auxiliary
theorems in the value of a definition but leaves them in its type, and the kernel is slow to
identify the two forms. Over a general `F` there is nothing to move. -/
def aInfToBCris (hε : PreTilt.untilt ε = 1) : AInf F p →+* BCris hε :=
  (algebraMap (BCrisPlus F p) (BCris hε)).comp
    ((algebraMap (ACris F p) (BCrisPlus F p)).comp (algebraMap (AInf F p) (ACris F p)))

end AInfToBCris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in

theorem iotaB_algebraMap_padic_bdRPlus (q : ℚ_[p]) :
    iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) q) = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap_padic q))

include hζ in

theorem iotaB_aInfToBCris (w : AInf ℂ_[p] p) :
    iotaB hε hζ (aInfToBCris hε w) =
      algebraMap 𝔹 𝔹dR (wittToBDeRhamPlus (normInteger ℂ_[p]) p w) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ ((iotaPlus_algebraMap _).trans (iota_algebraMap w)))

include hζ in

theorem iotaB_periodTCris_eq :
    iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (fontaineT ε hε) :=
  (iotaB_periodTCris hε hζ).trans (congrArg _ (iota_periodT hε))

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}



include hζ in

theorem isUnit_of_galB_fixed [FiniteDimensional ℚ_[p] L] {B : BCris hε} (hB0 : B ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/L), galB hε σ B = B) : IsUnit B := by
  obtain ⟨k, hk, hBk⟩ := bCris_fixed_mem_maxUnramified hε hζ (K := L) B h
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hB0
    apply iotaB_injective hε hζ
    rw [hBk, map_zero, map_zero, map_zero]
  obtain ⟨B', -, hB'⟩ := exists_bCris_fixed (K := L) hε hζ (inv_mem hk)
  have e : algebraMap 𝔹 𝔹dR (algClToBdR p k) * algebraMap 𝔹 𝔹dR (algClToBdR p k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk0, map_one, map_one]
  have h1 : B * B' = 1 := iotaB_injective hε hζ ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) hBk hB').trans (e.trans (map_one _).symm)))
  exact isUnit_iff_exists_inv.2 ⟨B', h1⟩

end ACris

end GroundTheory.PAdicHodge
