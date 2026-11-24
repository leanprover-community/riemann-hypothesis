module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)

def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩

end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Genus

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
