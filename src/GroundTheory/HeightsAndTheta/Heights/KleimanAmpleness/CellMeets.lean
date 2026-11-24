module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

open scoped Classical

open Classical in
def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0

def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1

def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)

def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)

abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
