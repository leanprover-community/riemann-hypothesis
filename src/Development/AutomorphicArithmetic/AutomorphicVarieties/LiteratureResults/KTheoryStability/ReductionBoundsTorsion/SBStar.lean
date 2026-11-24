module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

def WSys (R : Type) [CommRing R] (k j : ℕ) (a : ∀ n : ℕ, Chn (GL (Fin n) R) (k + 1) →ₗ[ℝ] ℝ) : Prop :=
  (∀ n z, IsBd z → a n z = 0) ∧
  (∀ n n' (h : n ≤ n') z, IsCyc z → a n' (cmap (stab R n n' h) (k + 1) z) = a n z) ∧
  ∀ d n z, 1 ≤ d → IsCyc z → a (d * n) (cmap (psi R d n) (k + 1) z) = (d : ℝ) ^ j * a n z

def SWt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N k : ℕ), Odd k → ∀ ω : Form (HS L N) (k + 1), (∀ g, FInv ω g) →
    ∃ a : ℕ → ∀ n : ℕ, Chn (Gm L n) (k + 1) →ₗ[ℝ] ℝ, (∀ j ∈ Finset.Icc 2 (k + 1), WSys (𝓞 L) k j (a j)) ∧
      ∀ z : Chn (Gm L N) (k + 1), IsCyc z →
        ev (emb L N) (intP ω) (one L N) z = ∑ j ∈ Finset.Icc 2 (k + 1), a j N z

def SSurj : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, k + 1 < nrComplexPlaces L → ∀ n₀ : ℕ,
    ∃ N, n₀ ≤ N ∧ ∀ c : (Fin (k + 2) → Gm L N) → ℝ, Inv (MonoidHom.id (Gm L N)) c → dC c = 0 →
      ∃ ω : Form (HS L N) (k + 1), (∀ g, FInv ω g) ∧ ∀ z : Chn (Gm L N) (k + 1), IsCyc z →
        ev (MonoidHom.id (Gm L N)) c 1 z = ev (emb L N) (intP ω) (one L N) z

def lev (l n : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => l * lev l n t

def zSeq (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (x : grpH (GL (Fin n) R) m) :
    ∀ t : ℕ, grpH (GL (Fin (lev l n t)) R) m
  | 0 => x
  | t + 1 => (grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
      l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom (zSeq R hl x t)

end PositivityTheory.KB

end
