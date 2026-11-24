module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecialStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem LawsLit.nu_eq_lpTw (H : LawsLit a ha e rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) :
    rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

end GlobalTheory.LocLanglands

namespace GlobalTheory

theorem lawsLit_det : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  intro hSC E Ω _ _ _ _ _ A w h a ha e rc H t χ hχ
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hL := GlobalTheory.T.isLanglandsClassification_detCharacter hSC (w.adicCompletion E) t χ hχ
  obtain ⟨φ⟩ := (IrrRep.det (Fin t) χ hχ).nonempty_equiv_rep
  have hL' := hL.of_equiv φ.symm
  rw [H.langlands _ (cls (IrrRep.det (Fin t) χ hχ)) hL', segSum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  show ((rc ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ))).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar
      (WD.lpSp (h := h) 1) = _
  have h0 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  rw [h0, (GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h _).1, H.nu_eq_lpTw]

end GlobalTheory
