module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrameStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Pre

variable (B : Pre)

theorem splitsC_level {p : ℕ} (hp : p ∈ B.host.levelPrimes) : SplitsC B.host.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem splitsC_g (k : Fin 2) : SplitsC B.host.E (B.host.g k) := B.splitsC_level (B.host.g_level k)

theorem splitsC_pde : SplitsC B.host.E B.host.pde := B.splitsC_level B.host.pde_level.1

theorem splitsC_pde' : SplitsC B.host.E B.host.pde' := B.splitsC_level B.host.pde_level.2

def EvenExp : Prop := ∀ j, UpperTheory.MUQ (embPsi B.host) (fun τ : B.R.Psi => (B.hc τ).e j)

theorem nonempty_hframe (h : B.EvenExp) : Nonempty (HFrame B.host fun j τ => (B.hc τ).e j) :=
  GlobalTheory.T.nonempty_hostHeckeCharacterFrame B.R B.host _ B.splitsC_g B.splitsC_pde B.splitsC_pde' (fun j τ => (B.hc τ).e_int j) h

end GlobalTheory.Mem.Pre

namespace GlobalTheory.Mem.Chr

end GlobalTheory.Mem.Chr

end
