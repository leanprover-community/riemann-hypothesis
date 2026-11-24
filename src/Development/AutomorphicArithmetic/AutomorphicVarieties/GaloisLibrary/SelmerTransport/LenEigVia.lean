module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigLe
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.lenEigVia :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q), Function.Surjective p →
      (∀ g, p g = 1 → ∀ x, π g x = x) →
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) ∧
      (IsUnit (Nat.card Q : O) → Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hfix
  have hker : p.ker ≤ MonoidHom.ker π := fun g hg =>
    (MonoidHom.mem_ker).mpr (LinearMap.ext (hfix g ((MonoidHom.mem_ker).mp hg)))
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  let π' : Representation O Q N := (QuotientGroup.lift p.ker π hker).comp e.symm.toMonoidHom
  have hπ' : ∀ g, π' (p g) = π g := by
    intro g
    have he : e.symm (p g) = (g : W ⧸ p.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift p.ker π hker (e.symm (p g)) = π g
    rw [he, QuotientGroup.lift_mk]
  have heig : ∀ ψ : Q →* Oˣ, eig π (ψ.comp p) = eig π' ψ := by
    intro ψ
    ext x
    simp only [mem_eig]
    constructor
    · intro h q
      obtain ⟨g, rfl⟩ := hp q
      rw [hπ']
      exact h g
    · intro h g
      rw [← hπ']
      exact h (p g)
  have hsum : ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))
      = ∑ ψ : Q →* Oˣ, Module.length O (eig π' ψ) :=
    Finset.sum_congr rfl fun ψ _ =>
      congrArg (fun S : Submodule O N => Module.length O S) (heig ψ)
  rw [hsum]
  exact ⟨lenEigLe O Q N π', fun hu => (lenEigEq O Q N π' hu).1⟩
