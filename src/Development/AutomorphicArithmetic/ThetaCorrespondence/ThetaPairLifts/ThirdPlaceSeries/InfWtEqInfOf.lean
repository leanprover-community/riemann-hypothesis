module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory.LocInfWt
theorem infWt_eq_infOf_alt : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  intro D M tup hH i a τ lam hd hw
  obtain ⟨P, -⟩ := D.naut.pt_surj i (Classical.arbitrary (D.nd.X i))
  rw [D.nbc.embAV_inf i P, hH.emb i P,
    hH.au.wt (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (hH.av.rep i P) a hd]
  exact hH.au.infW (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 a τ lam hw
end GlobalTheory.LocInfWt
end
