module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWildStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
