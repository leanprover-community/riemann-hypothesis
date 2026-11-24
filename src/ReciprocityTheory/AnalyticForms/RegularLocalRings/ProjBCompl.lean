module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

def projBCompl (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (projX P hP).Opens :=
  ⟨(projB P D hP : Set (projX P hP))ᶜ, (projB P D hP).isClosed.isOpen_compl⟩


variable (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) in
structure WData where

  W : Scheme.{0}
  π : W ⟶ projX P hP
  lft : LocallyOfFiniteType (π ≫ toSpecC hP)

  J : (projX P hP).IdealSheafData
  blowup : FinalTheorems.Blowup π J
  support_le : (J.support : Set (projX P hP)) ⊆ projB P D hP
  regular : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)
  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal
    ⟨π.base ⁻¹' (projB P D hP : Set (projX P hP)),
      IsClosed.preimage π.base.hom.continuous (projB P D hP).2⟩)
  isIso_off : IsIso (π ∣_ projBCompl P D hP)

  m : ((k : K) → ι k) → ℕ

  g : ∀ p, Fin (m p) → Γ(projX P hP, (chartOpen hP p).1)
  span_g : ∀ p, Ideal.span (Set.range (g p)) = J.ideal (chartOpen hP p)

  pres : ∀ p, Fin (m p) → AffPres (π ≫ toSpecC hP)
  le_pres : ∀ p i, (pres p i).V ≤ π ⁻¹ᵁ (chartOpen hP p).1
  iSup_pres : ∀ p, (⨆ i, (pres p i).V) = π ⁻¹ᵁ (chartOpen hP p).1

  t : ∀ p i, Fin (m p) → Γ(W, (pres p i).V)
  t_self : ∀ p i, t p i i = 1
  g_eq : ∀ p i k, π.appLE _ (pres p i).V (le_pres p i) (g p k) =
    t p i k * π.appLE _ (pres p i).V (le_pres p i) (g p i)
  inter : ∀ p i j, (pres p i).V ⊓ (pres p j).V = W.basicOpen (t p i j)
  t_cocycle : ∀ p i j k,
    W.presheaf.map (homOfLE (inf_le_right : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p j k) *
      W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i j) =
    W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i k)

  yq : ∀ p i, (Σ k, ι k) → Fin (pres p i).n

  yt : ∀ p i, Fin (m p) → Fin (pres p i).n
  sec_yq : ∀ p i q, (pres p i).secHom (X (yq p i q)) =
    π.appLE _ (pres p i).V (le_pres p i) (chartCoord hP p q)
  sec_yt : ∀ p i k, (pres p i).secHom (X (yt p i k)) = t p i k

  gen : ∀ p i (l : Fin (pres p i).n), ∃ F : MvPolynomial (Fin (pres p i).n) ℂ,
    F.vars ⊆ Finset.univ.image (yq p i) ∪ Finset.univ.image (yt p i) ∧ X l - F ∈ (pres p i).K

end

end ReciprocityTheory.AnForm.R
