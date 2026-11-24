module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace PositivityTheory.HtPt.Qak

theorem exists_pairEquiv {ι κ : Type} (e : ι ≃ κ) (m : κ → ℕ) (n : ι → ℕ) (h : ∀ s, m (e s) = n s) :
    ∃ g : (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) ≃ (Σ s, {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1}),
      ∀ (s : ι) (i j : Fin (m (e s))) (hij : i < j),
        g ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(Fin.cast (h s) j, Fin.cast (h s) i), hij⟩⟩ := by
  let e1 : (Σ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2}) ≃ (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) :=
    Equiv.sigmaCongrLeft (β := fun τ => {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) e
  let e2 : ∀ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2} ≃ {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1} := fun s =>
    { toFun := fun p => ⟨(Fin.cast (h s) p.1.2, Fin.cast (h s) p.1.1), p.2⟩
      invFun := fun p => ⟨(Fin.cast (h s).symm p.1.2, Fin.cast (h s).symm p.1.1), p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨e1.symm.trans (Equiv.sigmaCongrRight e2), fun s i j hij => ?_⟩
  have h1 : e1.symm ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(i, j), hij⟩⟩ := e1.symm_apply_apply ⟨s, ⟨(i, j), hij⟩⟩
  rw [Equiv.trans_apply, h1]
  rfl

theorem reindex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  intro E _ _ _ H Dw K L _ _ _ v hv
  obtain ⟨g, hg⟩ := exists_pairEquiv (Small.labelEquiv H) Dw.mult (labelRk Dw) (Small.mult_labelC Dw)
  refine ⟨(fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∘ g,
    hv.comp g g.injective, g.surjective.range_comp _, fun s i j hij => ?_⟩
  exact congrArg (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)
    (hg s i j hij)

end PositivityTheory.HtPt.Qak
