# writing-scalable-backends-in-udp

You are tasked with creating a client/server application in Golang that runs in Google Cloud. The client in this application must communicate with the server over UDP.

Each client sends 100 requests per-second. Each request is 100 bytes long. The server processes each request it receives and forwards it over HTTP to the backend.

The backend processes the request, and returns a response containing the FNV1a 64 bit hash of the request data. The server returns the response it receives from the backend down to the client over UDP.

Implement the client, server and backend in Golang. Provide an estimate of the cost to run the solution each month at a steady load of 1M clients, as well as some options you recommend as next steps to reduce the cost.

https://mas-bandwidth.com/writing-scalable-backends-in-udp-the-solution/