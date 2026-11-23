module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem charAt_eq_locChar_mul_locChar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h w' h' hne hall x
  have key : ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) *
      locIdele F w' (Units.map (toCompl h').toMonoidHom x) := by
    refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
    · rw [Units.val_mul, map_mul, infTens_locIdele, infTens_locIdele, mul_one]
      exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
    · rw [Units.val_mul, map_mul (finTens F E), map_mul, finTens_locIdele, finTens_locIdele]
      have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
          (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
        change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
        rw [← Algebra.TensorProduct.map_comp]
        rfl
      change _ = Neutral.B1.finiteSingle E w (Units.map (toCompl h).toMonoidHom x) u *
        Neutral.B1.finiteSingle E w' (Units.map (toCompl h').toMonoidHom x) u
      by_cases hu : u.under (𝓞 F) = v
      · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
        rcases (hall u).1 hu with rfl | rfl
        · rw [finSingle_self, finSingle_ne hne, mul_one]
          rfl
        · rw [finSingle_self, finSingle_ne (Ne.symm hne), one_mul]
          rfl
      · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one,
          finSingle_ne (fun e => hu (by rw [e]; exact h)), finSingle_ne (fun e => hu (by rw [e]; exact h')), mul_one]
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = _
  rw [key, map_mul]
  rfl

end GlobalTheory.LFun
