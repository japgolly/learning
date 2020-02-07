Exploring Requirements
======================


## Ch 2

* Relative cost to fix an error:

  | Phase in Which Found | Cost Ratio |
  | --- | --- |
  | Requirements | 1 |
  | Design | 3-6 |
  | Coding | 10 |
  | Dev testing | 15-40 |
  | Acceptance testing | 30-70 |
  | Operation | 40-1000 |

* Attack ambiguity because it costs. Early = low cost.


## Ch 3 – Sources of Ambiguity

* “How many points in the star?”
* The recall heuristic: Take away the written doc and ask readers to write down exactly what was written. Different answers = ambiguity. Good because most people * will just go off memory of the doc, rather than checking the doc all the time.
* Factors responsible for different recollections:
  * Observational errors (didn’t look properly)
  * Recall errors (looked but didn’t retain)
  * Interpretation errors
  * Effects of human interaction


## Ch 4 – The Tried and Untrue Use of Direct Questions

* “Design a transportation device.”


## Ch 5 – Starting Points

* A problem is best defined as a difference between things as perceived and things as desired.
* Starting points:
  * Solution ideas => what’s the problem?
  * Technology ideas => what problems could it solve?
  * Similes => Brainstorm into solid ideas
  * Norm (Based ideas on some existing norm)
  * Mockup
  * Name (There is a great, inspiring name)


## Ch 6 – Context-Free Questions

* General
  * Who is the client?
  * What is a highly successful solution really worth to the client?
  * What is the real reason for wanting to solve this problem?
  * Who should be on the team(s)?
  * How much time do we have for this product?
  * What is your trade-off between time and value?
  * Where else can the solution to this design be obtained?
  * Can we copy something that already exists?
* Product questions
  * What problems does this product solve?
  * What problems could this product create?
  * What environment is this product likely to encounter?
  * What kind of precision is required or desired in the product?
* Metaquestions
  * Am I asking too many questions?
  * Do my questions seem relevant?
  * Are you the right person to answer these questions?
  * Are your answers official?
* End of interaction
  * Is there anything else I should be asking you?
  * Is there anything you would like to ask me?
  * May I return or call you with more questions later, in case I don’t cover everything this time?
* Other
  * I noticed that you hesitated a long time before answering that question. Is there something else we should know?
  * When I asked X about that, she said Y. Do you have any idea why she might’ve said Y?
  * I notice you don’t seem to agree with that reply. Would you tell us about that?


## Ch 9 – Reducing Ambiguity…

* To uncover ambiguity
  * Emphasise each word
  * Replace words with similes
  * Take polls and confirm all responses in the right bucket


## Ch 12 – Project Name

* Naming heuristic:
  1. Pick a name.
  2. Choose 3 reasons why the name is inadequate.
  3. Create a new name that fixes those 3 reasons.
  4. Back to #2, repeat a few times and stop (it won’t be perfect).
* Use dictionary and thesaurus
* Create acronym


## Ch 14 – Fucntions

* H – Hidden – Don’t care how, only care about the (blackbox) result.
* E – Evident – You can see how it does what it does.
* F – Frill – Would like at zero cost/impact.
* “The best” is the enemy of “the good”. Don’t always aim for the best, evaluate whether good or not without comparing to the best.


## Ch 15 – Attributes

* Attributes = adverbs, adjectives.
* Do this:
  1. Brainstorm adverbs and adjectives into a list.
  2. Distinguish:
    * Attribute – definition – “colour”
    * Attribute details – values – “blue”
  3. Resolve ambiguity
  4. Make a list of [Attribute] = (list of [Attribute Details]). Example:
    * Color = (blue, cyan, aqua, green)
  5. Think of each attribute applied to each function in order to discover more requirements.
* Assign each attribute: (M)ust have, (W)ants to have, (I)gnorable.


## Ch 16 – Constraints

* Create constraints for each (M) attribute
* Tilt! Crash against boundaries and constraints to test their veracity.


## Ch 17 – Preferences

* Preferences come from the client, not the designer
* Only the strength of the clients fears or desires determines which is a constraint and which is a preference.


## Ch 21 – Measuring Satisfaction

* Survey users. No questions, just bipolar attributes. E.g. `Easy to Use [ ][ ][ ][ ][ ] Hard to use`
* Graph min, avg, max scores over time.


## Ch 22 – Test cases

* Coverage
  1. Normal use of the function.
  2. Abnormal but reasonable use of the function.
  3. Abnormal and unreasonable use of the function.
* Creating test cases can reveal more requirements.


## Ch 23 – Studying existing products

* New products will be compared to existing ones using the metrics that the existing ones are measured by, (even in inappropriate). E.g. early telephone being measured by words-per-minute, until one guy started singing over the telephone.
* When comparing new and existing productions, compare the functions, not the features. (One function can result in many features.)