module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrictStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover
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

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => GlobalTheory.T.hilbert_point_eq_of_open_cover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
