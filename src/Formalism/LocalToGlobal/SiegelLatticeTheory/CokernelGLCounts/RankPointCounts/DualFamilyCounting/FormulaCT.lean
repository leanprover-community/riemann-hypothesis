module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowLatEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TotallyPositiveAll
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

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormulaCT : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M),
    Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.MainNotions.S.Cnt.Stand D u u' →
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) (cExpl D (T.X.Fu u) (T.Y.what₂ u))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaCT_of (hF : DualityBasisChange.FrameBasisL) : FormulaCT := by
  intro D T u u' Lsp hLT _ hT
  have hη : AtD.EtaLocAt D := fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hLT p
  have hDA := AtD.densAllAt_of D hF hη
  have hFE := Formalism.L2.SG.Pf.formulaExplicitAt_of D hDA
  have hR := T.Y.rowsOK u
  obtain ⟨Λ0, hΛ0⟩ := lattice_exists_holds D T u
  have hne : (T.Y.what₂ u).Nonempty := by
    obtain ⟨Λ', ⟨hΛ', -⟩, -⟩ := hR.2 Λ0 hΛ0
    exact ⟨Λ', hΛ'⟩
  refine ⟨cExpl_pos' D u (T.X.Fu u) (T.Y.what₂ u) hR hne, fun ϖ hϖ Z =>
    ⟨orbitFiniteR_of counting_iso_inverse D T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR Z,
      fun hP => ⟨?_, ?_⟩⟩⟩
  · obtain ⟨F', hz, hZ⟩ := rational_pair_holds D u u' hT (T.X.Fu u) (T.Y.what₂ u) hR Z hP
    obtain ⟨h1, h2⟩ := hDA T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR ϖ hϖ Z F' hz hZ hP
    by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D (T.X.Fu u) F')
    · exact (h1 hI).2
    · obtain ⟨p, hp⟩ := h2 hI
      exact (hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).multipliable
  · exact hFE T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR ϖ hϖ Z hP

end Formalism.L2.SG.Pf.Cnt
