Questions for eliciting business requirements
=============================================

  **What business problem are you trying to solve?**
  This question helps align subsequent requirements development and software development activities with the right objective.

  **What's the motivation for solving this problem?**
  Team members work together more effectively if they understand the rationale behind their work.

  **What would a highly successful solution do for you?**
  Management should be able to state the benefits they and their customers will receive from the product.

  **How can we judge the success of the solution?**
  People often don't think about how they will determine whether some enterprise has been successful. Contemplating this evaluation early on helps crystallize the stakeholders' thinking about objectives and steers the project toward a clearly successful outcome.

  **What's a successful solution worth?**
  Whenever possible, quantify the business outcomes (Wiegers 2002b). All projects involve some cost-benefit analysis. Understanding the potential return in measurable units helps participants make cost-effective decisions.

  **Who are the individuals or groups that could influence this project or be influenced by it?**
  This question seeks to identify potential stakeholders in the project. These stakeholders might need to be consulted to understand their interests in the project, their expectations, and the nature of their involvement.

  **Are there any related projects or systems that could influence this one or that this project could affect?**
  Look for dependencies between projects and systems that need to be analyzed and accommodated. Sometimes small changes can have huge ripple effects across multiple interconnected systems.

  **Which business activities and events should be included in the solution? Which should not?**
  These questions help define the scope boundary. Modifying the established project scope is a business decision that has implications for cost, schedule, resources, quality, and tradeoff decisions. See Chapter 17, "Defining Project Scope," for suggestions about how to document the scope boundary.

  **Can you think of any unexpected or adverse consequences that the new system could cause?**
  Consider whether certain individuals, organizations, customers, or business processes could experience a negative impact from the system or product being developed. For example, a new information system that automates a process that has been performed manually in the past could threaten the job stability of the people who perform that process. Employees might need retraining, or their job descriptions could change, both of which could lead to resistance to the project and unwillingness to cooperate.



Questions for eliciting user requirements
=========================================

  **What are some reasons why you or your colleagues would use the new product?**
  These "reasons to use" could become candidates for use cases. They might identify business tasks or objectives that members of a particular user class might need to achieve from time to time.

  **What goals might you have in mind that this product could help you accomplish?**
  Use cases normally are directed toward helping the user achieve a specific goal. The name of the use case indicates the goal the user has in mind: Print a Boarding Pass, Withdraw Cash, Calibrate Pressure Meter, Submit an Employment Application, and so on. Users can't always articulate their goals directly, though. Observation and other techniques, such as contextual inquiry (Beyer and Holtzblatt 1998), might be necessary to discover what users really expect.

  **What problems do you expect this product to solve for you?**
  Understanding the problems and limitations the users perceive in their current environment helps analysts determine the appropriate capabilities for the new system. This question also helps determine whether the end users' objectives for the system align well with senior management's objectives, as captured in the business requirements. Users might expect the system to do something for them that is out of scope according to senior management's judgment. Such a disconnect points to the need for iteration between the business requirements and user requirements levels. The key stakeholders must hold aligned expectations for the new or modified product.

  **What external events are associated with the product?**
  Analysts sometimes use the term business event to describe the triggering condition that launches execution of a use case. Perhaps a help desk receives a phone call from a user who needs assistance. This external event triggers the help desk staffer to create a problem report ticket. Create Problem Report Ticket is a good name for a use case. In other types of products, such as real-time control systems, use cases are not a valuable technique for understanding user requirements. An alternative approach is to identify the external events the system must detect. Then describe the appropriate system response, which depends on the state the system is in at the time each event is detected. See Chapter 11, "When Use Cases Aren't Enough," for more about events.

Most requirements discussions focus on functionality.
However, a product's nonfunctional characteristics also have a great impact on how users feel about the product.
Questions such as the ones that follow help the analyst understand the user's expectations about aspects of the product's quality.

  **What words would you use to describe the product?**
  Consider asking users to close their eyes and describe their vision of the future system. Listen to the words they use to describe the product. Nouns suggest objects the system must be able to manipulate (such as order, reservation, chemical, account balance, sensor). Verbs can indicate actions the user expects to be able to take or expects the system to take (such as place, create, revise, submit, receive, detect, measure, display). Adverbs convey the user's thoughts about the product's characteristics (for example, quickly, reliably, efficiently, flexibly, easily). Use this input to better understand what the user considers to be important about the product.

  **Are specific portions of the product more critical than others for performance, reliability, security, safety, availability, or other characteristics?**
  As much as we might like to, software developers can never create a product that combines the maximum levels of all quality characteristics. Tradeoffs are necessary between properties such as usability and efficiency, integrity and usability, and integrity and interoperability. Therefore, it's important to understand which specific portions or aspects of the product have critical quality demands so that the developers can optimize their designs to achieve those objectives. Sure, everyone would like 100 percent availability in all locations, but that's not realistic. It's quite likely that certain system functions or use case flows have more stringent availability requirements than others. Certain flows will have rigid response-time requirements, but others will not be time-critical. Perform this same analysis for the other quality attributes.

  **Are there any constraints or rules to which the product must conform?**
  Most products are subject to corporate policies and technical standards, industry standards, government laws and regulations, and other external constraints. These are collectively referred to as business rules. (See Chapter 21, "Business Requirements and Business Rules.") It's essential to know about the pertinent business rules so that analysts can specify functional requirements to enforce or comply with those rules. Don't expect users to present all these rules spontaneously. The analyst needs to identify where such rules are likely to be pertinent and to explicitly ask users about them. Business rules sometimes fit into a company's oral tradition or folklore; the rules are very real but they might not be documented. Look for subject matter experts within the organization who have current knowledge about the business rules.

  **How is the product you envision similar to the way you do business now? How should it be different?**
  When automating current business processes or replacing an existing information system with a new one, it's easy to inadvertently re-implement all the shortcomings of the current approaches. This is known as "repaving the cow paths." It's difficult for people to break from the mindset of their current ways of working and to envision something that's really different and better. The analyst should stimulate the thinking of the user representatives to help them fully exploit this opportunity to devise better ways of working. Rethink business rules and business processes to see what has changed—or what could change.

  **What aspects of the current product or business process do you want to retain? To replace?**
  This question is similar to the previous one. Customer acceptance of a new product depends partly on how comfortable and familiar it feels to them. Similarity to previous products and processes reduces the learning curve, making it easier for users to master a new system and workflow. Knowing which aspects of the current business process or software system irritate the users reveals opportunities for improvements that will delight customers.

The following questions also help the analyst gain a richer understanding of how potential users view the product.
Asking these questions of people who represent different stakeholder groups can reveal disconnects or conflicts that must be reconciled when defining and prioritizing the product's functionality.

  **Which aspects of the product are most critical to creating business value?**
  A user's view of business value might be different from a manager's view or an acquiring customer's view. A user might value a more efficient way to perform a specific task that will save considerable time over many executions. A manager, on the other hand, could be more impressed if the product has lower acquisition and support costs than the one it is replacing.

  **What aspect of the product most excites you?**
  The answers to this sort of question help analysts determine what product characteristics or capabilities could be powerful enablers of customer acceptance.

  **What aspect of the product will be most valuable to you? Least valuable?**
  No project can deliver everything to everybody on day one. Someone needs to prioritize, to determine the sequence in which to implement various capabilities. Ask this question of different user representatives, and look for patterns that indicate certain product capabilities are more important and more urgent than others. Those capabilities should have top priority.

  **What is most important to you about the product?**
  The deliberately general way this question is phrased could generate responses dealing either with the product itself or with other aspects of the project. One user might say, "It's most important that this system be available before the beginning of the next fiscal year." Another user might respond, "It's most important that this system will let me import all my data from these older systems we've been using." A manager might say, "It's most important that the people in my department can get up to speed on this new system with little or no training." These responses have implications for how the project is planned, the product functionality to include, and usability, respectively.

  **How would you judge whether the product is a success?**
  A business manager might judge the success of the product quite differently from how members of different user classes determine success. Surface these different perspectives early so that they can be reconciled and so that you keep all stakeholders working toward a common objective.

  **Can you describe the environment in which the product will be used?**
  The operating environment has a big impact on both requirements and design decisions. The operating environment will provide information about possible external interfaces that must be constructed. The user interface is also highly sensitive to the operating environment. Touch screen displays are superior to keyboards in some settings, for example, and speech recognition is becoming increasingly effective. But speech recognition wouldn't work well in an environment with a lot of background noise.



Context-Free Questions
======================

* **General**
  * Who is the client?
  * What is a highly successful solution really worth to the client?
  * What is the real reason for wanting to solve this problem?
  * Who should be on the team(s)?
  * How much time do we have for this product?
  * What is your trade-off between time and value?
  * Where else can the solution to this design be obtained?
  * Can we copy something that already exists?
* **Product questions**
  * What problems does this product solve?
  * What problems could this product create?
  * What environment is this product likely to encounter?
  * What kind of precision is required or desired in the product?
* **Metaquestions**
  * Am I asking too many questions?
  * Do my questions seem relevant?
  * Are you the right person to answer these questions?
  * Are your answers official?
* **End of interaction**
  * Is there anything else I should be asking you?
  * Is there anything you would like to ask me?
  * May I return or call you with more questions later, in case I don’t cover everything this time?
* **Other**
  * I noticed that you hesitated a long time before answering that question. Is there something else we should know?
  * When I asked X about that, she said Y. Do you have any idea why she might’ve said Y?
  * I notice you don’t seem to agree with that reply. Would you tell us about that?
