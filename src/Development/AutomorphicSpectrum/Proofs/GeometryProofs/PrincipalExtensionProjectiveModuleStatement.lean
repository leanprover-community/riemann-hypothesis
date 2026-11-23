module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField


theorem _root_.GlobalTheory.T.principal_extension_projective_module : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | exact GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension <;> assumption)
