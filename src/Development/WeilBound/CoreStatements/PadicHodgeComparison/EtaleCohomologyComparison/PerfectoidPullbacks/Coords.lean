module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure QMor (Φ : PDF R C) (Φ' : PDF R C') (c : IdF Φ'.A) where
  G : C' ⥤ C
  ρ : ∀ T : C', Φ.A.obj (G.obj T) →ₐ[R] Φ'.A.obj T ⧸ c.S T
  inj : ∀ T, Function.Injective (ρ T)
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : Φ.A.obj (G.obj T)) (y : Φ'.A.obj T), ρ T x = Ideal.Quotient.mk _ y →
    ρ T' ((Φ.A.map (G.map φ)).hom x) = Ideal.Quotient.mk _ ((Φ'.A.map φ).hom y)
  dp : ∀ (T : C') (k : ℕ) (x : Φ.A.obj (G.obj T)) (y : Φ'.A.obj T), x ∈ Φ.J.S _ → y ∈ Φ'.J.S T → ρ T x = Ideal.Quotient.mk _ y →
    ρ T (Φ.dp k x) = Ideal.Quotient.mk _ (Φ'.dp k y)

variable {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

def QMor.o (m : QMor Φ Φ' c) (b : IdF Φ'.A) (h : ∀ T, c.S T ≤ b.S T) :
    CH.Mor (CH.modF Φ.A) (sq (IdF.top Φ'.A) b) (RingHom.id R) where
  G := m.G
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (h T) (m.ρ T x), by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.factor (h T) (m.ρ T x))
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (by
        change Ideal.Quotient.factor (h T) (m.ρ T ((show Φ.A.obj _ from x) + (show Φ.A.obj _ from y))) = _
        rw [map_add (f := _), map_add (f := _)]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        change Ideal.Quotient.factorₐ R (h T) (m.ρ T (r • (show Φ.A.obj _ from x))) = r • Ideal.Quotient.factorₐ R (h T) (m.ρ T x)
        rw [map_smul, map_smul]) }
  nat φ x := by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (m.ρ _ x)
    refine Subtype.ext ?_
    change Ideal.Quotient.factor (h _) (m.ρ _ ((Φ.A.map (m.G.map φ)).hom x)) =
      Ideal.quotientMapₐ _ (Φ'.A.map φ).hom (fun _ hx => b.map_mem φ hx) (Ideal.Quotient.factor (h _) (m.ρ _ x))
    rw [m.nat φ x y hy.symm, ← hy]
    rfl

def QMor.Fr (m : QMor Φ Φ' c) {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Φ') d)
    (e : E.D ⟶ m.G.obj E'.D) : Prop :=
  ∀ (i : Fin d) {T : C'} (s s' : E'.D ⟶ T), m.ρ T (E.τ i (e ≫ m.G.map s) (e ≫ m.G.map s')) = Ideal.Quotient.mk _ (E'.τ i s s')

def Frame.Coords {d : ℕ} (E : Frame (Φ := Φ) d) (t : Fin d → Φ.A.obj E.D) : Prop :=
  ∀ (i : Fin d) {T : C} (s s' : E.D ⟶ T), E.τ i s s' = (Φ.A.map s').hom (t i) - (Φ.A.map s).hom (t i)

end CrystallineSemistableComparison.Pb
