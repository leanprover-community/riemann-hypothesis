module

public import Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleOpenCovSieve : Prop := ∀ (T : Scheme.{0}) (S : Sieve T),
  (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ S V.ι) → S ∈ Scheme.etaleTopology.{0} T

def EtaleAugInjAt : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ)
    (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).obj T)),
    Cyc _ n T x → Bdy _ n T ((((chainsP R).map (aug _ hc)).f n).app T |>.hom x) →
    ∀ t : T.unop, ∃ V : T.unop.Opens, t ∈ V ∧
      Bdy _ n (op (V : Scheme.{0})) (((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).map V.ι.op).hom x)

theorem bdy_res {R : Type} [CommRing R] (K : PCx R) (n : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : (K.X n).obj (op U))
    (h : Bdy K n (op U) x) : Bdy K n (op V) (((K.X n).map g.op).hom x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨((K.X (n + 1)).map g.op).hom y, ?_⟩
  have := (K.d (n + 1) n).naturality g.op
  exact (ConcreteCategory.congr_hom this y).symm.trans rfl |>.symm ▸ rfl

def bdySieve {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}) (x : (K.X n).obj (op T)) : Sieve T where
  arrows U f := Bdy K n (op U) (((K.X n).map f.op).hom x)
  downward_closed {U V} f hf g := by
    have e : ((K.X n).map (g ≫ f).op).hom x = ((K.X n).map g.op).hom (((K.X n).map f.op).hom x) := by
      rw [op_comp, Functor.map_comp]; rfl
    rw [e]; exact bdy_res K n g _ hf

theorem EtaleAugInj_of_openCovSieve (hc0 : EtaleOpenCovSieve) (ha : EtaleAugInjAt) : LeafAugInj := by
  intro J _ D X c ho hcov hdir hc R _ n T x hx hb
  refine ⟨bdySieve _ n T.unop x, hc0 _ _ fun t => ?_, fun U f hf => hf⟩
  obtain ⟨V, hV, h⟩ := ha J D X c ho hcov hdir hc R n T x hx hb t
  exact ⟨V, hV, h⟩

theorem etaleOpenCovSieve : EtaleOpenCovSieve := by
  intro T S h
  choose V hV hS using h
  apply Scheme.zariskiTopology_le_etaleTopology
  rw [Scheme.zariskiTopology, Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun t => (V t : Scheme.{0})) (fun t => (V t).ι)
    (fun x => ⟨x, ⟨x, hV x⟩, by simp⟩), ?_⟩
  rintro Y g ⟨i⟩
  exact hS i

theorem EtaleAugInj_of_augInjAt (ha : EtaleAugInjAt) : LeafAugInj := EtaleAugInj_of_openCovSieve etaleOpenCovSieve ha

end LateralTheory.CohomologicalPurity.TubeCut
