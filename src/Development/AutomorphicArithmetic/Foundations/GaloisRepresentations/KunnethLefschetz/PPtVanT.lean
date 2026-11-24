module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
public import Development.EtaleCohomology.EtaleTrace.PtCoverPf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sec_of {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ S k) (hf : Etale f)
    (hs : Surjective f) : ∃ s : S k ⟶ Y, s ≫ f = 𝟙 _ := by
  have hmem : Sieve.generate (Presieve.singleton f) ∈ Scheme.etaleTopology (S k) := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨y, rfl⟩ := hs.surj u
    exact ⟨Y, f, y, hf, rfl, ⟨Y, 𝟙 Y, f, Presieve.singleton.mk, Category.id_comp f⟩⟩
  obtain ⟨Z, h, g, hg, hcomp⟩ := PtCover_of k _ hmem
  cases hg
  exact ⟨h, hcomp⟩

theorem ptVanT_holds : PtVanT := by
  intro hIn k _ _ q n i hn
  have hzero : ∀ x : Ht q (sch.obj (S k)) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hIn.a5 (ZMod q) (S k) (tw q i) n hn x
    obtain ⟨s, hsf⟩ := sec_of f hf hs
    calc x = pull (ZMod q) (𝟙 (sch.obj (S k))) (tw q i) n x := (pull_id _ _ _ _ x).symm
      _ = pull (ZMod q) (sch.map s ≫ sch.map f) (tw q i) n x := by
        rw [← CategoryTheory.Functor.map_comp, hsf, CategoryTheory.Functor.map_id]
      _ = pull (ZMod q) (sch.map s) (tw q i) n (pull (ZMod q) (sch.map f) (tw q i) n x) :=
        pull_comp _ _ _ _ _ x
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end UpperTheory.Gal.KunnethLefschetz
