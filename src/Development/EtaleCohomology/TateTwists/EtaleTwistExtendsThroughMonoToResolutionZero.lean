module

public import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add (f := _)]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
