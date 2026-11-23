module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsFurther
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace DualStdGenDeg

def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩

theorem eq_fibreBlk₀ (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h

def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h

theorem range_eq {T Φ' : Type} [Field Φ'] {i : ℕ} (x' : (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → Φ') (d : Φ') :
    (Set.range fun p : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
        fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k) => x' ⟨p.1.1, p.2⟩ / d) =
      Set.range fun t : T => x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / d := by
  ext y
  constructor
  · rintro ⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩
    · exact ⟨t, rfl⟩
    · exact absurd ⟨(), rfl⟩ h
  · rintro ⟨t, rfl⟩
    exact ⟨⟨fibreBlk₀, t⟩, rfl⟩

end DualStdGenDeg


open DualStdGenDeg in
theorem DualStdGenDeg.proof (hPt : OneBlockPointDeg.Statement) (hRat : DualStdFibreRatios.Statement) :
    DualStdGenDeg.Statement := by
  intro K _ _ i T _ _ b G J hi hJ
  obtain ⟨c, hc, hrank, htr⟩ := hRat K i T b G hi
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
      G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
        G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) :=
    Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have key := hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀
    (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc
  beta_reduce at key
  rw [range_eq G.x'] at key
  obtain ⟨hV, hch, hdeg⟩ := key hfin htr
  have hJ0 := hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch
  rw [hJ0]
  exact congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)

end GroundTheory.Heights₂.Heights
