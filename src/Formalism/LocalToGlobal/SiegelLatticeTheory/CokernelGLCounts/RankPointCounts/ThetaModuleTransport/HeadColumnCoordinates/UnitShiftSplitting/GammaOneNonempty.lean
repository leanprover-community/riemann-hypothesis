module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem gammaOne_nonempty {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R)
    (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Gam1 hs Z TT Zm).Nonempty :=
  ⟨_, 0, 0, rfl⟩

theorem gamSplit_of (hsub : GamSubP) (hsup : GamSupP) : GamSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk θ₁ θ₂ _ _
  have e₁ : GR g Zh₁ T T' = asm hs h₁ '' (Gam1 hs Z₁ TT (ZZm g Zh₁ T T') ×ˢ
      Gam1 hs Zσ₁ TT (ZZm g (Zh₁.map M.L.cj) T T')) :=
    Set.Subset.antisymm (hsub F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁)
      (hsup F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁)
  have e₂ : GR g Zh₂ T T' = asm hs h₂ '' (Gam1 hs Z₂ TT (ZZm g Zh₂ T T') ×ˢ
      Gam1 hs Zσ₂ TT (ZZm g (Zh₂.map M.L.cj) T T')) :=
    Set.Subset.antisymm (hsub F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂)
      (hsup F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂)
  change _ '' GR g Zh₁ T T' = GR g Zh₂ T T' ↔ _
  rw [e₁, e₂, Set.image_image]
  simp_rw [asm_compat hs h₁ h₂ hk θ₁ θ₂]
  rw [← Set.image_image (asm hs h₂) (Prod.map (mapD θ₁) (mapD θ₂)),
    (Set.image_injective.mpr (asm_inj hs h₂)).eq_iff]
  have hp : (fun p => (mapD (M := M) θ₁ p.1, mapD (M := M) θ₂ p.2)) = Prod.map (mapD (M := M) θ₁) (mapD (M := M) θ₂) := rfl
  rw [← hp, ← Set.prod_image_image_eq, Set.prod_eq_prod_iff_of_nonempty]
  · rfl
  · exact (((gammaOne_nonempty hs _ _ _).image _).prod ((gammaOne_nonempty hs _ _ _).image _))

end Formalism.L2.SG.LocalCountModules.AlgGSplit
