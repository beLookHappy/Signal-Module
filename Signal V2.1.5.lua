--!optimize 2
--!native
--[[
	Name: LSignal

	/-----------------------------\
	|         S I G N A L         |
	\-----------------------------/
	
	A Luau-Based Signal Implementation

	Linked list:
	head -> [] -> [] -> [] -> [] <- tail
	
	@Author : Lkkyuy (LookHappy)	
	@Date   : 8/13/2025	
	@Update : 8/16/2025
	@Version: 2.1.5
	V 2.1.5	Updates:
	1. Fixed DisconectAll failed when enable parallel
	
	V 2.1.0 Updates:
	1. Optimized performance
	
	V 2.0.0 Updates:
	1. Improved quality
	2. Organized variables
	
	V 1.5.0 Updates:
	1. Support for multiple Actors
	2. Defensive programming
	
	V 1.0.0 Updates:
	1. Added Signal:ConnectParallel()
	2. Added Signal:FireParallel()
	3. Added Signal:FireDeferred()
	
	V 0.7.5 Updates:
	1. Added Signal:Destroy()
	2. Added Signal:DisconnectAll()
	3. Fixed "self" var will lose when connection disconnects
	4. Fixed delete()
	
	V 0.5.0 Updates:
	1. Added Signal:Wait()
	2. Rewrote the module - Use the LinkedList instead of Block Linked List
	
	V 0.3.5 Updates:
	1. Added Type annotations
	2. Changed Logic
	
	V 0.1 Updates:
	1. demo

	
	APIs:
	Signal.new() -- Create a Signal Object
	-> Signal:Connect -- Connect function
	-> Signal:Fire -- Call all connections
	-> Signal:Wait -- Wait for Fire
	-> Signal:Once -- Connect once
	-> Signal:DisconnectAll -- Disconnect all
	-> Signal:Destroy -- Destroy Signal Object
	-> Signal:ConnectParallel -- Connect function with parallel call
	-> Signal.isEmpty -- Signal connections list is empty
	SignalConnection:Disconnect() -- Disconnect connection
	
]]
--[[

	The MIT License 

	Copyright (c) 2025 Lkkyuy

	Permission is hereby granted, free of charge, to any person obtaining a copy of this 
	software and associated documentation files (the ¡°Software¡±), to deal in the Software
	without restriction, including without limitation the rights to use, copy, modify,
	merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
	permit persons to whom the Software is furnished to do so, subject to the following 
	conditions:

	The above copyright notice and this permission notice shall be included in all copies
	or substantial portions of the Software.

	THE SOFTWARE IS PROVIDED ¡°AS IS¡±, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
	INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
	PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
	HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
	OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
	SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

]]
--[[ LOCAL FUNCTIONS FROM GLOBAL LIBRARIES ]]
local table_insert = table.insert
local table_clear = table.clear
local SharedTable_new = SharedTable.new
local SharedTable_clear = SharedTable.clear
local SharedTable_size = SharedTable.size
local SharedTable_update = SharedTable.update
local coroutine_resume = coroutine.resume
local coroutine_create = coroutine.create
local coroutine_yield = coroutine.yield
local coroutine_close = coroutine.close	 
local task_spawn = task.spawn
local task_defer = task.defer
local task_desynchronize = task.desynchronize
local debug_info = debug.info
local string_split = string.split
local string_sub = string.sub
local table_freeze = table.freeze
local table_isfrozen = table.isfrozen
--[[ SERVICES ]]
local SharedTableRegistry = game:GetService("SharedTableRegistry")
--local sharedMAs = SharedTableRegistry:GetSharedTable("_SIGNAL_") or SharedTable.new()
--SharedTableRegistry:SetSharedTable("_SIGNAL_", sharedMAs)

--[[ TYPES ]]
export type SignalConnection = {
	Connected: boolean,
	Disconnect: (self: any) -> ()
}

export type Signal<T...> = {
	Connect: (self: any, func: (T...) -> ()) -> SignalConnection,
	ConnectParallel: (self: any, func: (T...) -> ()) -> SignalConnection,
	Once: (self: any, func: (T...) -> ()) -> SignalConnection,
	Wait: (self: any) -> T...,
	DisconnectAll: (self: any) -> (),
	Destroy: (self: any) -> (),
	isEmpty: boolean,
	isEmptyParallel: boolean?,
	EnabledParallel: boolean,
	GetListenersCounter: (self: any) -> number,
	GetListenersCounterParallel: (self: any) -> number,
}
export type SignalClass<T...> = {
	Fire: (self: any, T...) -> (),
	FireDeferred: (self: any, T...) -> (),
	FireParallel: (self: any, T...) -> (),
} & Signal<T...>

export type SignalModule = {
	new: <T...> (uniqueEnableMultipleActorsName: string?) -> SignalClass<T...>,
	Fire: <T...> (self: any, T...) -> ()
}
--[[ UTILS ]]
local function handleCallAndThread(con, func, ...)
	local current_thread = con._freeEventThread
	con._freeEventThread = nil
	func(...)
	con._freeEventThread = current_thread
end
--[[
	EventConnectionLoop
	Job: Handle the Signal connection loop when call .Fire().
]]
local function runEventConnectionLoop(con)
	while true do
		handleCallAndThread(con, coroutine_yield())
	end
end

local function delete(self)
	for k,v in pairs(self) do
		self[k] = nil
	end
end

--[[
	[interface Class]
	ISignalConnection
	
	Properties:
		Connected [boolean] 
	Methods:
		Disconnect 	

]]

--[[ FLAGS ]]
export type SignalFlag = number
local SIGNAL_FLAG_DEFAULT  = 0x0000
local SIGNAL_FLAG_ONCE     = 0x0001
local SIGNAL_FLAG_WAITING  = 0x0002
local SIGNAL_FLAG_PARALLEL = 0x0003

--[[
	[Class]
	SignalConnection
	
	based on ISignalConnection
	
	A connection to a signal.
	It's as a LinkedList Node and a Instance.
]]
local SignalConnection = {}
SignalConnection.__index = SignalConnection

-- I like xxx.new() not xxx:new()

--[[
	Notes:
	I didn't type most functions because it's better to have types
	that are open to the outside and optional to the inside
]]

function SignalConnection.new<T...>(signal: Signal<T...>, func: (T...) -> (), flag: SignalFlag, thread: thread)

	local self = {

		_func = func,
		_signal = signal,
		Connected = true,
		_freeEventThread = nil, 
		_next = nil,
		_prev = nil,
		_flag =  flag or SIGNAL_FLAG_DEFAULT,
		_thread = thread or nil,
		--_topic = nil,

	}
	return setmetatable(self, SignalConnection)
end
--[[
	A part of LinkedList
	Job: Remove Node
]]
local function Signal_remove_node(self, connection)
	--[[
		connection:
		[...] <-> [connection] <-> [...]
			  /	
		<- : _prev
		-> : _next
	]]
	local con_next = connection._next
	local con_prev = connection._prev
	if con_prev then
		con_prev._next = con_next
	end
	if con_next then
		con_next._prev = con_prev
	end
end

function SignalConnection_disconnect(self)
	
	if not self.Connected then
		return
	end

	self.Connected = false
	local signal = self._signal
	signal._counter -= 1
	if signal._counter == 0 then
		signal.isEmpty = true
	end

	Signal_remove_node(signal, self)
	
	delete(self)
end

function SignalConnection:Disconnect()
	-- yep just get the real data
	-- I hate wrapping it 
	SignalConnection_disconnect(getmetatable(self).__getRealData())

end

--[[
	Signal
	Core Class
]]
local Signal = {
	ClassName = "Signal"
}
Signal.__index = Signal

--[[
	uniqueMAsName 
	Job: Store the SharedTable key
	Why do I devised it?
		1. I want to make it unique
		2. As a parameter instead of starting a new stove is 
		   the best memory saver
		3. Users can choose for themselves 
]]
-- MAs : Multiple Actors
function Signal.new(uniqueMAsName: string?)

	local self = {
		_head = nil,
		_tail = nil,
		isEmpty = true,
		EnabledParallel = uniqueMAsName ~= nil,
		_counter = 0,
	}
	if uniqueMAsName then
		local sharedMAsKey = `_SIGNAL_{uniqueMAsName}`
		local sharedMAs = SharedTableRegistry:GetSharedTable(sharedMAsKey) 
		if not sharedMAs then
			sharedMAs = SharedTable_new()
			SharedTableRegistry:SetSharedTable(sharedMAsKey, sharedMAs)
		end
		self.isEmptyParallel = true
		self._signalParallelConnections = {}
		self._parallelCounter = 0
		self._sharedMAsKey = sharedMAsKey
		self._sharedMAs = sharedMAs	
	end

	return setmetatable(self, Signal)
end
function Signal:GetListenersCounter()
	return self._counter
end
function Signal:GetListenersCounterParallel()
	return self._parallelCounter
end
function Signal:Fire(...)

	local current_pointer = self._head 
	-- iter the list
	while current_pointer ~= nil do
		--[[
			Keep it in line with the Roblox style, so use Connected as the state
			instead of using a flag
			Old (before v0.5) : isActive
			New (after v0.5)  : Connected
		]]
		if current_pointer.Connected then
			local flag = current_pointer._flag
			--[[
				flag is a kind of Enum ?
				not all right.
			]]
			--[[
				C is the best
			]]
			if flag == SIGNAL_FLAG_WAITING then
				coroutine_resume(current_pointer._thread, ...)
				current_pointer = current_pointer._next
				continue
			end
			--[[
			
				Here, I designed to assign a separate thread to each connection,
				because after a new signal, the connection is often long and short,
				because Fire will traverse the entire list, so when designing only
				one thread for the signal, you need to check the status, and then
				frequently create and wait for it to come back	
			
			]]
			
			local current_freeThread = current_pointer._freeEventThread
			-- init thread
			if not current_freeThread then
				current_pointer._freeEventThread = coroutine_create(runEventConnectionLoop)
				coroutine_resume(current_pointer._freeEventThread, current_pointer)
			end
			-- call it and give a function
			local func = current_pointer._func
			task_spawn(current_pointer._freeEventThread, func, ...)
			-- check flag
			if flag == SIGNAL_FLAG_ONCE then
				current_pointer:Disconnect()
			end	
		end
		-- here we go to a next stop !
		current_pointer = current_pointer._next
	end

end
--[[
	Job: Insert Node	
	For LinkedList
]]
local function Signal_insert_node(self, new_connection)
	if self.isEmpty then
		self._head, self._tail = new_connection, new_connection
		self.isEmpty = false
		return new_connection
	end
	local tail = self._tail
	self._tail._next = new_connection
	new_connection._prev = tail		
end
--[[
	Wait() uses the same sibling scheme as Connect() to ensure FIFO
]]
function Signal:Wait()
	self._counter += 1
	local new_connection = SignalConnection.new(self, nil, SIGNAL_FLAG_WAITING, coroutine.running())
	Signal_insert_node(self, new_connection)
	return coroutine_yield()
end

-- scriptSoruceInfo, a good name
local scriptSoruceInfo = debug_info(1, "s")

--[[
	Proxy Connection and Hook for security purposes
]]
local function CONNECTION_HOOK_PROXY(target)

	local proxy = {}
	local proxy_mt = table_freeze({

		__index = function(t, k)

			if string_sub(k, 1, 1) == "_" then
				if debug_info(2, "s") ~= scriptSoruceInfo then
					return
				end
			end
			return target[k]
		end,

		__newindex = function(t, k ,v)
			if string_sub(k, 1, 1) == "_" then
				if debug_info(2, "s") ~= scriptSoruceInfo then
					return
				end
			end
			target[k] = v
		end,

		__getRealData = function()
			if debug_info(2, "s") ~= scriptSoruceInfo then
				return
			end
			return target
		end,

	})


	return setmetatable(proxy, proxy_mt)
end


function Signal:Connect(func)
	assert(func and type(func) == "function", 
		`Invalid argument #1 to "Connect" (function execpted, {typeof(func)} got)`
	)
	self._counter += 1
	local new_connection = SignalConnection.new(self, func, SIGNAL_FLAG_DEFAULT)
	Signal_insert_node(self, new_connection)
	return CONNECTION_HOOK_PROXY(new_connection)
end

function Signal:Once(func)
	assert(func and type(func) == "function", 
		`Invalid argument #1 to "Once" (function execpted, {typeof(func)} got)`
	)
	self._counter += 1
	local new_connection = SignalConnection.new(self, func, SIGNAL_FLAG_ONCE)
	Signal_insert_node(self, new_connection)
	return CONNECTION_HOOK_PROXY(new_connection)
end

function Signal:FireDeferred(...)
	task_defer(self.Fire, self, ...)
end

--[[
	Parallel Part
]]

function Signal:FireParallel(...)
	local enabledParallel = self.EnabledParallel
	assert(enabledParallel,
		`"FireParallel" method can only be called by beEnabledParallel Signal`
	)
	local sharedMAs = self._sharedMAs
	-- SHIT SHAREDTABLE 
	if SharedTable_size(sharedMAs) == 0 then
		return
	end
	-- fine 
	for connectionKey: string, currentSources in sharedMAs do
		if not currentSources then
			continue
		end
		local connectionSrcsArray = string_split(currentSources, ".")
		local currentService = game:FindService(connectionSrcsArray[1])
		local currentActor = nil
		local instanceIndex: Instance = currentService
		local scriptIndex = nil
		
		for i=2, #connectionSrcsArray do
			instanceIndex = instanceIndex:FindFirstChild(connectionSrcsArray[i])
		end
		scriptIndex = instanceIndex
		
		if not scriptIndex then
			continue
		end
		
		currentActor = scriptIndex:GetActor()
		if not currentActor then
			continue
		end
		-- let's send it 
		currentActor:SendMessage(connectionKey, ...)
	end
end
--[[
	[Class]
	SignalParallelConnection
	
	based on ISignalConnection
	
	The difference between SignalParallelConnection and SignalConnection is
	that the structure is different: the former uses array storage, the latter 
	uses linked list storage, and they are separated because the Fire methods
	are inconsistent

]]
local SignalParallelConnection = {}
SignalParallelConnection.__index = SignalParallelConnection
function SignalParallelConnection.new(signal, func, actor, connectionSources, connectionKey)

	local self = {
		_signal = signal,
		Connected = true,
		_connectionSources = connectionSources,
		_connection = actor:BindToMessageParallel(connectionKey, func)
	}
	return setmetatable(self, SignalParallelConnection)
end

local function SignalParallelConnection_disconnect(self)
	
	if not self.Connected then
		return
	end
	self._signal._parallelCounter -= 1 
	if self._signal._parallelCounter < 1 then
		self._signal.isEmptyParallel = true
	end
	self.Connected = false
	local connectionSources = self._connectionSources

	self._connection:Disconnect()

	delete(self)
end

function SignalParallelConnection:Disconnect()
	SignalParallelConnection_disconnect(getmetatable(self).__getRealData())
end

function Signal:ConnectParallel(scriptSourceContainer: LuaSourceContainer, func)
	local enabledParallel = self.EnabledParallel
	assert(enabledParallel,
		`"ConnectParallel" method can only be called by beEnabledParallel Signal`
	)
	assert(scriptSourceContainer and scriptSourceContainer:IsA("LuaSourceContainer"), 
		`Invalid argument #1 to "ConnectParallel" (LuaSourceContainer execpted, {typeof(scriptSourceContainer)} got)`)
	assert(func and type(func) == "function", 
		`Invalid argument #1 to "ConnectParallel" (function execpted, {typeof(func)} got)`
	)
	local sharedMAs = self._sharedMAs
	local sharedMAsKey = self._sharedMAsKey
	local actor = scriptSourceContainer:GetActor()

	local connectionSources = debug_info(2, "s")
	local connectionKey = connectionSources .. sharedMAsKey 

	if not actor then
		error(`Attempt to call "ConnectParallel" method under a non-Actor parent instance`)
	end

	SharedTable_update(sharedMAs, connectionKey, function(oldValue)
		if oldValue == nil then
			return connectionSources
		end
		return oldValue
	end)


	local connection = SignalParallelConnection.new(self, func, actor, connectionSources, connectionKey)
	local signalParallelConnections = self._signalParallelConnections
	self.isEmptyParallel = false
	self._parallelCounter += 1

	table_insert(signalParallelConnections, connection)
	task_desynchronize()
	return CONNECTION_HOOK_PROXY(connection)
end


function Signal:DisconnectAll()
	local current_pointer = self._tail
	while current_pointer ~= nil do
		SignalConnection_disconnect(current_pointer)
		current_pointer = current_pointer._prev
	end
	
	local enabledParallel = self.EnabledParallel

	if not enabledParallel then
		return
	end
	
	local parallelConnections = self._signalParallelConnections
	local parallelConnectionsLength = #self._signalParallelConnections
	if parallelConnectionsLength > 1 then

		for i=1, parallelConnectionsLength do

			SignalParallelConnection_disconnect(parallelConnections[i])
		end
		table_clear(parallelConnections)
	end
	
	SharedTable_clear(self._sharedMAs)
end
function Signal:Destroy()
	self:DisconnectAll()

	delete(self)
	setmetatable(self, {})
end
--[[
	We need to make sure it's type safe
	Strict inspection
]]
if table_isfrozen(Signal) == false then
	table_freeze(Signal)
end	

return Signal :: SignalModule