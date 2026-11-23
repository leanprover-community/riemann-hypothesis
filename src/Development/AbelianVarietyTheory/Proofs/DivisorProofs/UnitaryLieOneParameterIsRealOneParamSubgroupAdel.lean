module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
open Matrix GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UAut

theorem isRealLine_oneP (D : D7) (θ : InfF D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) :
    GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  obtain ⟨-, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hZ : Xᴴ * V.gram.map (embOverOf D τ).1 + V.gram.map (embOverOf D τ).1 * X = 0 := hX
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine (isCMExt_host D) (h2 V) (embOverOf D τ) hZ
  refine ⟨placeOf D τ, embOverOf D τ, X, hZ, fun t => ⟨_, ?_, hγ t⟩⟩
  rw [oneP, ← hγ t, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]

end GlobalTheory.UAut
