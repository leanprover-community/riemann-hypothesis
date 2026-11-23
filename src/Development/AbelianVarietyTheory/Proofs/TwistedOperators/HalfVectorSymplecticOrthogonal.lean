module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodinge
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OrthOff

theorem orthOff : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  intro D _ T L μ0 _ sc G W M _ e he S T' LS LT u hu y hy
  classical
  have hx : FinPl.MxAt (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) (y.map (cA D)) :=
    GlobalTheory.PlaceModelComb.mxAt_of_idemSum he (Or.inr fun i j => by
      rw [Matrix.map_apply, ← map_mul, hy i j])
  have hu' := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hoff : ∀ i j, u i j ∈ FinPl.idOff D (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    intro i j
    rw [FinPl.idOff, Ideal.mem_iInf]
    rintro ⟨w, PP, hPP, rfl⟩
    have hin : HeightOneSpectrum.under (𝓞 D.host.F) PP ∈ G.pl.S0 := by
      unfold Places.W0 at hPP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
      rw [G.pl.under_w hv]
      exact hv
    have h := hu' i j
    rw [FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at h
    exact h.2 ⟨_, fun h' => h' hin⟩
  have hh : hO S T' u y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * u d a = 0 :=
      GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hx c b) (hoff d a)
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T'.gram c d) * u d a
        = incA D (S.gram⁻¹ a b) * incA D (T'.gram c d) * (cA D (y c b) * u d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

end GlobalTheory.OrthOff
