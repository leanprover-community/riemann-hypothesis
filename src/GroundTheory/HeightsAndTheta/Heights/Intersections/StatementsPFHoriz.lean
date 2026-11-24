module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩

def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W

end Fibre

def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

end

end GroundTheory.Heights₂.Heights.Inter
