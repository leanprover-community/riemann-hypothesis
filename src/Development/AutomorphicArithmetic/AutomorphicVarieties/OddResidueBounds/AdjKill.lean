module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.AlgebraMapSignedInvolutionQuotientDetMemSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.adjKill :
    ∀ (A Γ X : Type) [CommRing A] [CommGroup Γ] [Finite Γ] [AddCommGroup X] [Module A X] (π : Representation A Γ X) (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ (z : MonoidAlgebra A Γ) (x : X), π c x = (ε : A) • x → π.asAlgebraHom z x = 0 → detR c ε z • x = 0 := by
  intro A Γ X _ _ _ _ _ π c ε hc hc1 hε z x hx hz
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (algebraMap_signedInvolutionQuotientDet_mem_span (A := A) c ε hc hc1 hε z)
  have hrel : π.asAlgebraHom (rel A c ε) x = 0 := by
    simp [rel, hx, Int.cast_smul_eq_zsmul]
  have key := congrArg (fun w => π.asAlgebraHom w x) hab
  simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm
