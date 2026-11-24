module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePairStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddingsStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem away_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact GlobalTheory.T.kernelSite_away_of_positive_pair S hD ⟨J.alg0, J.alg⟩ J.kin (GlobalTheory.T.site_place_induces_position_embeddings S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hD)

end GlobalTheory.TwV
