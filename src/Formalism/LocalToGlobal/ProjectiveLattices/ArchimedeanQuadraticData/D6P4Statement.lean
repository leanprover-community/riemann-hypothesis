import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FundamentalDomainD5
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FrameAtMaximumOfTransference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalShortVectorBoundOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainOfTransference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxPointFrameOfTransference

set_option autoImplicit false

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]




theorem t41H_statement : ReciprocityTheory.ChartRestriction.G.FD.FrameAtHalfMaximum (E := E) :=
  ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_transference d5_translation


end Formalism.L2.Pj.FundamentalDomainD5
