module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.AdjointKernelOpen

variable {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] {F : Frame l κ} {C : Type} [CommRing C]

private theorem r_ker_open (hdel : IsOpen (F.del.ker : Set F.Γ)) (B : Box F 3 C)
    (h : ∀ i j, IsLocallyConstant fun s => (B.r s).mat i j) : IsOpen (B.r.ker : Set F.Γ) := by
  have hset : (B.r.ker : Set F.Γ) = (F.del.ker : Set F.Γ) ∩
      ⋂ i, ⋂ j, (fun s => (B.r s).mat i j) ⁻¹' {(1 : Matrix (Fin 3) (Fin 3) C) i j} := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [← B.nu s]
    constructor
    · intro hs
      refine ⟨by rw [hs]; rfl, fun i j => ?_⟩
      rw [hs]
      rfl
    · rintro ⟨h1, h2⟩
      apply SemidirectProduct.ext
      · apply Units.ext
        ext i j
        exact h2 i j
      · exact h1
  rw [hset]
  exact hdel.inter (isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (h i j).isOpen_fiber _)

end UpperTheory.V.Z.J.AdjointKernelOpen

open UpperTheory.V.Z.J.AdjointKernelOpen in
theorem UpperTheory.V.Z.J.adOpen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (B : Box F 3 O) (k : ℕ), B.Cont (maximalIdeal O) → IsOpen ((adK B k).ker : Set F.Γ) := by
  intro l _ O _ _ _ _ _ F C₀ hF hl B k hB
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨N, hN⟩ := (okFin l O hl).2.2.2.2.1 k
  have hK : IsOpen ((boxK B k).r.ker : Set F.Γ) := by
    refine r_ker_open hF.del_open (boxK B k) fun i j => ?_
    have hc := (hB i j N).comp (Ideal.Quotient.factor hN)
    convert hc using 1
    funext s
    simp [Ideal.Quotient.factor_mk, boxK, Box.map, GG.map, GG.mat]
  refine Subgroup.isOpen_mono (fun s hs => ?_) hK
  rw [MonoidHom.mem_ker] at hs ⊢
  ext x
  simp [adK, Box.ad, adRep, hs]
