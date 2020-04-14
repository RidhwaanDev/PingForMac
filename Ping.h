#pragma once

#include <sys/socket.h>

class NetworkDriver;
class Ping {
 public:
	Ping(std::string name) : hostname(name) {}
	NetworkDriver& initNetworkDriver() const; 
    void sendPing();
 private:
	std::string hostname;
    uint32_t packetLoss;
	uint32_t packetsTransmitted;  
	uint32_t packetsRecieved;  
};

// holds all structs needed for networking
class NetworkDriver  {
 
};
