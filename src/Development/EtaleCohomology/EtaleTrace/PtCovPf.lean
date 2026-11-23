module

public import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
