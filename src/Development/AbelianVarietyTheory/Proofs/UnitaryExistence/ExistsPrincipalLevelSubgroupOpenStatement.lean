module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_principalLevel_subgroup_open : ∀ (D : D7) (V : HSp D), ∀ N : ℕ, (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧ (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) := by
  first | exact @GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds
