window.SIDEBAR_ITEMS = {"enum":[["CircuitRelayClientError",""],["CreationError","Errors that might happen during network creation."],["GetClosestPeersError",""],["PeerSyncStatus","Defines peer synchronization status."],["PieceKey",""],["RelayMode","Defines relay configuration for the Node"],["SendRequestError",""],["SubscribeError",""]],"fn":[["create","Create a new network node and node runner instances."],["peer_id","Converts public key from keypair to PeerId. It serves as the shared PeerId generating algorithm."],["start_prometheus_metrics_server","Start prometheus metrics server on the provided address."]],"mod":[["utils",""]],"struct":[["BootstrappedNetworkingParameters","Networking manager implementation with bootstrapped addresses. All other operations muted."],["Config","[`Node`] configuration."],["CustomRecordStore",""],["GenericRequestHandler",""],["GetOnlyRecordStorage","Hacky replacement for Kademlia’s record store that doesn’t store anything and instead proxies gets to externally provided implementation."],["LimitedSizeRecordStorageWrapper","Record storage decorator. It wraps the inner record storage and monitors items number."],["MemoryProviderStorage","Memory based provider records storage."],["MemoryRecordStorage","Memory based record storage."],["NetworkingParametersManager","Handles networking parameters. It manages network parameters set and its persistence."],["NoRecordStorage","Defines a stub for record storage with all operations defaulted."],["Node","Implementation of a network node on Subspace Network."],["NodeRunner","Runner for the Node."],["ObjectMappingsRequest","Object-mapping protocol request."],["ObjectMappingsResponse","Object-mapping protocol request."],["ParityDbRecordStorage","Defines record storage with DB persistence"],["PeerInfo","Defines peer current state."],["PeerInfoRequest","Peer-info protocol request."],["PeerInfoResponse","Peer-info protocol response."],["PieceByHashRequest","Piece-by-hash protocol request."],["PieceByHashResponse","Piece-by-hash protocol response."],["PiecesByRangeRequest","Pieces-by-range protocol request. Assumes requests with paging."],["PiecesByRangeResponse","Pieces-by-range protocol response. Assumes requests with paging."],["PiecesToPlot","Collection of pieces that potentially need to be plotted"],["TopicSubscription","Topic subscription, will unsubscribe when last instance is dropped for a particular topic."]],"trait":[["GenericRequest","Generic request with associated response"],["RecordStorage",""]],"type":[["ObjectMappingsRequestHandler","Create a new object-mappings request handler."],["PeerInfoRequestHandler","Create a new peer-info request handler."],["PieceByHashRequestHandler","Create a new piece-by-hash request handler."],["PiecesByRangeRequestHandler","Create a new pieces-by-range request handler."]]};