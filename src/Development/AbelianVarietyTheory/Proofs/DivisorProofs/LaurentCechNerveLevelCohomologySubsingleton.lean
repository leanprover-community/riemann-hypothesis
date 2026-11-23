module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebraStatement
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
