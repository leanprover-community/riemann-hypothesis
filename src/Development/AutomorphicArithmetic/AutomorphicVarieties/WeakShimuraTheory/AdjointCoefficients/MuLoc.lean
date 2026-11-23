module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GenOfMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuBock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.muLoc :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ ζ, MuGen (Dec (F := F) A) (muOf l (Dec (F := F) A)) ζ := by
  intro P F Ω _ _ _ _ _ l _ A hA
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  obtain ⟨-, h1, h2, -⟩ := Kum.placeDict F Ω
  obtain ⟨v, hv⟩ := h1 A (h2 A l hl.ne_zero hA)
  have hc : ReciprocityTheory.Gal.ContAction (charRep (1 : Dec (F := F) A →* (ZMod l)ˣ)) := by
    have e : (fun p : Dec (F := F) A × ZMod l => charRep (1 : Dec (F := F) A →* (ZMod l)ˣ) p.1 p.2) = Prod.snd := by
      funext p
      exact one_mul p.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact continuous_snd
  obtain ⟨-, f2, -, -, e2⟩ := GC.locEuler P.loc.lf P.loc.lt P.loc.le F Ω l v A hv (ZMod l) (ZMod l) _ hc
  refine X1.muCyc l _ (isClosed_Dec A) (X1.muBock l _ (isClosed_Dec A) (Module.finite_of_finite (ZMod l)) ?_)
  rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod, e2]
  refine (Nat.pow_le_pow_right hl.pos ((Submodule.finrank_le _).trans ?_)).trans_eq (pow_one l)
  rw [Subspace.dual_finrank_eq, Module.finrank_self]
