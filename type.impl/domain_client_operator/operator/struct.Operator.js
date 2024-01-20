(function() {var type_impls = {
"domain_service":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Operator%3CBlock,+CBlock,+Client,+CClient,+TransactionPool,+Backend,+E%3E\" class=\"impl\"><a href=\"#impl-Operator%3CBlock,+CBlock,+Client,+CClient,+TransactionPool,+Backend,+E%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt; Operator&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt;<div class=\"where\">where\n    Block: Block,\n    &lt;Block as Block&gt;::Hash: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;H256&gt;,\n    CBlock: Block,\n    &lt;&lt;CBlock as Block&gt;::Header as Header&gt;::Number: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&lt;&lt;Block as Block&gt;::Header as Header&gt;::Number&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;&lt;&lt;Block as Block&gt;::Header as Header&gt;::Number&gt;,\n    &lt;CBlock as Block&gt;::Hash: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&lt;Block as Block&gt;::Hash&gt;,\n    Client: HeaderBackend&lt;Block&gt; + BlockBackend&lt;Block&gt; + AuxStore + ProvideRuntimeApi&lt;Block&gt; + ProofProvider&lt;Block&gt; + Finalizer&lt;Block, Backend&gt; + 'static,\n    &lt;Client as ProvideRuntimeApi&lt;Block&gt;&gt;::Api: DomainCoreApi&lt;Block&gt; + MessengerApi&lt;Block, &lt;&lt;Block as Block&gt;::Header as Header&gt;::Number&gt; + BlockBuilder&lt;Block&gt; + ApiExt&lt;Block&gt; + TaggedTransactionQueue&lt;Block&gt;,\n    CClient: HeaderBackend&lt;CBlock&gt; + HeaderMetadata&lt;CBlock, Error = Error&gt; + BlockBackend&lt;CBlock&gt; + ProvideRuntimeApi&lt;CBlock&gt; + ProofProvider&lt;CBlock&gt; + BlockchainEvents&lt;CBlock&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'static,\n    &lt;CClient as ProvideRuntimeApi&lt;CBlock&gt;&gt;::Api: DomainsApi&lt;CBlock, &lt;Block as Block&gt;::Header&gt; + MessengerApi&lt;CBlock, &lt;&lt;CBlock as Block&gt;::Header as Header&gt;::Number&gt; + BundleProducerElectionApi&lt;CBlock, <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u128.html\">u128</a>&gt; + FraudProofApi&lt;CBlock, &lt;Block as Block&gt;::Header&gt;,\n    Backend: Backend&lt;Block&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'static,\n    TransactionPool: TransactionPool&lt;Block = Block&gt; + 'static,\n    E: CodeExecutor,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.new\" class=\"method\"><h4 class=\"code-header\">pub async fn <a class=\"fn\">new</a>&lt;IBNS, CIBNS, NSNS, ASS&gt;(\n    spawn_essential: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html\" title=\"struct alloc::boxed::Box\">Box</a>&lt;dyn SpawnEssentialNamed&gt;,\n    params: OperatorParams&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E, IBNS, CIBNS, NSNS, ASS&gt;\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Operator&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt;, Error&gt;<div class=\"where\">where\n    IBNS: Stream&lt;Item = (&lt;&lt;CBlock as Block&gt;::Header as Header&gt;::Number, Sender&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>&gt;)&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    CIBNS: Stream&lt;Item = BlockImportNotification&lt;CBlock&gt;&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    NSNS: Stream&lt;Item = (Slot, <a class=\"struct\" href=\"subspace_core_primitives/struct.Randomness.html\" title=\"struct subspace_core_primitives::Randomness\">Randomness</a>)&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    ASS: Stream&lt;Item = Sender&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>&gt;&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div></h4></section></summary><div class=\"docblock\"><p>Create a new instance.</p>\n</div></details><section id=\"method.fraud_proof_generator\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">fraud_proof_generator</a>(\n    &amp;self\n) -&gt; FraudProofGenerator&lt;Block, CBlock, Client, CClient, Backend, E&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.import_notification_stream\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">import_notification_stream</a>(\n    &amp;self\n) -&gt; TracingUnboundedReceiver&lt;DomainBlockImportNotification&lt;Block, CBlock&gt;&gt;</h4></section></summary><div class=\"docblock\"><p>Get system domain block import notification stream.</p>\n<p>NOTE: Unlike <code>BlockchainEvents::import_notification_stream()</code>, this notification won’t be\nfired until the system domain block’s receipt processing is done.</p>\n</div></details></div></details>",0,"domain_service::domain::DomainOperator"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-Operator%3CBlock,+CBlock,+Client,+CClient,+TransactionPool,+Backend,+E%3E\" class=\"impl\"><a href=\"#impl-Clone-for-Operator%3CBlock,+CBlock,+Client,+CClient,+TransactionPool,+Backend,+E%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for Operator&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt;<div class=\"where\">where\n    Block: Block,\n    CBlock: Block,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(\n    &amp;self\n) -&gt; Operator&lt;Block, CBlock, Client, CClient, TransactionPool, Backend, E&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#169\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","domain_service::domain::DomainOperator"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()